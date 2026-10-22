# static

Check Raku types at compile time using the current compilation unit's RakuAST.
Requires Rakudo **2026.09 or newer**, with the RakuAST frontend enabled (the
standard frontend in these releases). No external dependencies.

```raku
use static;
CHECK fail-on-mismatch;

sub message() { 'hello' }
my Int $number = message();
# Compilation fails: expected Int, got Str:D
```

`use static` only imports the API. Call one checker explicitly in a `CHECK`
phaser in **each compilation unit** you want to validate. Run `raku -Ilib -c
program.raku` to check a program without running its mainline. Normal Raku
compile-time activity, such as the program's own `BEGIN` blocks, still happens.

## Command line

Check existing files without adding `use static` or a `CHECK` phaser:

```sh
raku bin/static-check.raku program.raku other.raku
cat program.raku | raku bin/static-check.raku
raku bin/static-check.raku --policy=fail-on-unverifiable program.raku
raku bin/static-check.raku --/check-methods program.raku
```

With no files, or with `-` as a filename, the command reads stdin. Each file is
compiled independently; imported units are not analyzed. Original file paths and
line numbers are preserved. All inputs are checked even when an earlier one
fails. Exit status is 0 on success, 1 for compilation/checking or input failures,
and 2 for invalid command options. The default policy is `fail-on-mismatch`;
`--policy` accepts any of the four policies below.
`--/check-unreachable` disables unreachable-code diagnostics. `--/external-signatures` and
`--/check-methods` disable the corresponding checks. Module search paths can be
provided through `RAKULIB` as usual. Interpreter `-I` search paths are also
forwarded to the compiler:

```sh
raku -Ilib -I../OtherProject/lib bin/static-check.raku ../OtherProject/lib/Example.rakumod
```

The command itself also accepts repeated `-I` and `-M` options, using attached,
separate, or `=` arguments. `-M` loads a module and imports its exports into each
input unit, just like the interpreter option:

```sh
bin/static-check.raku -Ilib -I../OtherProject/lib -MExample program.raku
bin/static-check.raku -I lib -M Example -M AnotherModule program.raku
```

The command uses compile-only mode: mainline code does not run, but normal
compile-time activity (`BEGIN`, `CHECK`, imports, etc.) still runs.

## Policies

| Function | Reports | Effect |
| --- | --- | --- |
| `warn-on-mismatch` | Proven incompatibilities | Warnings |
| `fail-on-mismatch` | Proven incompatibilities | Compilation failure |
| `warn-on-unverifiable` | Incompatibilities and inconclusive checks | Warnings |
| `fail-on-unverifiable` | Incompatibilities and inconclusive checks | Compilation failure |

All four accept an optional positional `RakuAST::CompUnit` (default `$*CU`)
and the Boolean options `:external-signatures`, `:check-methods`, and
`:check-unreachable` (all default to `True`):

```raku
CHECK warn-on-unverifiable($*CU, :!external-signatures);
```

With external signatures enabled, the checker reads available contracts of
imported routines and CORE routines. It never traverses their bodies or infers
their returns from external ASTs. Disabling the option makes those calls
inconclusive. Intrinsic CORE operator rules and control-flow rules remain
available.

Method existence is checked by default on known exact class objects and instances,
including inherited methods. A missing method is a mismatch. Receivers that may
be subclasses, `FALLBACK`, qualified method names, and optional dispatch (`.?` / `.*`) remain inconclusive;
the checker does not execute dynamic method providers. Disable the existence
check with any policy:

```raku
CHECK fail-on-mismatch(:!check-methods);
```

This option only suppresses missing-method diagnostics. Existing method argument
checks remain active, and an unknown method return used in a typed assignment
can still be inconclusive under a strict policy.

Code proven unreachable after a terminating expression is reported as
`[static:unreachable]` by all four policies: warnings for `warn-*`, compilation
failure for `fail-*`. Only the first executable statement in each unreachable
region is reported. Routine, package, handler and phaser declarations are not
classified as dead executable statements. Disable this diagnostic with
`CHECK fail-on-mismatch(:!check-unreachable)` or CLI `--/check-unreachable`.
Disabling diagnostics does not make unreachable statements affect inference.

```raku
sub example() {
    return 42;
    say "unreachable"; # [static:unreachable]
}
```

Diagnostics contain `[static:mismatch]`, `[static:unverifiable]`, or
`[static:unreachable]`, source
file/line when available, and the relevant types or reason for uncertainty.
Warnings continue compilation and can be handled with Raku's usual warning
handlers. Failing modes collect selected problems and register a
`static::CheckFailure` compilation error, whose `.diagnostics` contains the
diagnostic objects. The compiler rejects the unit after the `CHECK` phasers;
the checker does not throw from the phaser itself. The error points at the
first offending expression, without a `CHECK` wrapper or internal backtrace.
All checkers return the selected diagnostics as a `List`.
The exception can be imported as `CheckFailure` with `use static :DEFAULT, :types`.

## Inference

Constant conditions eliminate unreachable branches, including ternaries,
statement modifiers and short-circuit expressions. Supported nominal type tests
and CORE `.defined` tests refine branch-local facts; primitive integer comparisons
also establish inclusive bounds used by later arithmetic and predicates.
Assignments and potentially mutating calls invalidate those assumptions.
Custom `ACCEPTS` and potentially overridden `.defined` methods do not establish
nominal or definedness refinements.

The checker tracks lexical declarations by identity, initializations,
assignments, branch joins, bounded loop iteration, calls and return paths.
For local routines without an explicit return contract, it collects explicit
and implicit returns and combines their types with **`(@types).are`**:

```raku
sub value(Bool $fraction) {
    $fraction ?? 1/2 !! 1
}
# Inferred ancestor: Real

sub identity($value) { $value }
# Inferred return: Any, from the parameter's default type.
# Calling identity(42) does not specialize the routine's return to Int.
```

Alternatives are retained internally: losing precision through `.are` does not
by itself prove an incompatibility. At call sites of routines without a return
contract, mixed compatible and incompatible inferred returns are inconclusive.
For a declared return contract, every alternative in the body is checked:
a known incompatible return is a mismatch even if another return fits.
Forward calls and mutually recursive routines
are resolved through bounded fixed-point iteration; unresolved recursion is
inconclusive.

Explicit contracts, including `returns`, take precedence at call sites and are
checked against the local routine's body. The pass does not rewrite the AST,
add return annotations, or replace Raku's runtime checks.

## Coverage and limits

Supported checks include scalar/attribute initialization, assignments and
bindings, routine arguments and defaults, positional/named/optional/slurpy
parameters, method calls, multi candidates, and declared returns. Typed array
and hash initializations and indexed writes are checked, as are recognized
array insertion methods. Nominal inheritance, roles, definedness constraints,
parameterized contracts, subsets, coercion types and native contracts are
considered. Direct `::T` captures are bound across arguments and return contracts;
nominally more specific multi candidates are preferred when that ordering is
statically established. Typed hash keys and lexical aliases are checked too.

CORE `.pick` and `.roll` on known built-in lists and arrays retain possible
element types, including `Nil` for a possibly empty scalar selection.
`("bla", 42).pick` and `.roll` can return `Str` or `Int`, so each violates a
`--> Int` return contract. Integer count arguments and `*` produce sequence
facts with element contracts and a known cardinality when established; random
order is never invented, and nonempty `.roll(*)` is recorded as infinite.

CORE `map`, `grep` and `first` analyze known single-element callbacks, including
inline blocks, routine references and single-argument Whatever expressions.
Finite inputs retain exact results when established, up to 256 elements;
larger inputs use element summaries. Lazy sequences and finite captures lose
content assumptions when a known source or alias changes. Analysis never
executes callbacks. Mutable
captures use declared contracts and callback writes invalidate caller assumptions.
`pop` and `shift` track known removed elements and update shared container
references. Empty removal yields `Failure`, whose use in a typed assignment is
checked. Functional CORE forms of `map`, `grep`, `first`, `pick`, `roll`, `pop` and `shift` use
these rules too. Custom methods retain ordinary dispatch analysis.

Known lexical routine references and parenthesized callable expressions are
checked through their resolved signatures and local return summaries. Known
closures also bind positional/named/slurpy arguments and propagate captured
writes. Deferred callbacks with nonlocal returns remain inconclusive. Finite
captures can supply both positional and named arguments through `|`. Direct
`::T` captures can be substituted recursively into built-in `Array`, `List`,
`Positional`, `Hash` and `Associative` contracts, including nested parameters.
Actual container contracts are respected: an untyped `[1]` is not `Array[Int]`.

Simple local `where`/subset predicates are analyzed using primitive constants,
comparisons, arithmetic, Boolean combinations, intervals, type junctions,
`*.chars`, `*.defined`, known collection lengths, and references to previously
bound signature parameters. For example:

```raku
sub positive(Int $x where * > 0) { $x }
positive(-1);                         # proven mismatch
my Int $x where * > 0 = -1;           # proven mismatch
subset Small of Int where 1..10;
my Small $s = 20;                    # proven mismatch
```

The analyzer interprets only a bounded allowlist of pure primitive operations.
It does not invoke the compiled predicate, arbitrary calls, overloaded
operators, regexes, or user coercions.

Container and effect checks also cover:

- Writes to readonly scalar parameters (including aliases, increments and
  compound assignments), and writable arguments for `is rw`. `is copy` permits
  local writes; `is raw` needs runtime container information.
- Finite positional destructuring declarations and assignments, nested routine
  sub-signatures, slurpy declaration tails, lexical bindings and recognized
  array/hash element bindings. Dynamic sources, proxies and more complex
  binding lifetimes can remain inconclusive.
- `given`/`when`/`default` paths with known type, literal or Boolean conditions;
  `try`, `CATCH` and `CONTROL` bodies, including explicit returns and loss of
  value assumptions after exceptional paths. Arbitrary smartmatch predicates
  and exact resumption are not proven. Known exceptions from explicit `die`
  and local callees select compatible nominal `CATCH` arms; unknown external
  exceptions retain conservative possibilities. Returns, throws and process
  exit are tracked separately; `try` consumes exceptional paths.
- The elements yielded by `gather`/`take`, values of `start` observed through
  `await` or `.result`, and `supply`/`emit` values checked against inline `tap`
  callback signatures. Mutable captures use declared contracts rather than
  current values; deferred writes invalidate caller assumptions. This does not
  prove scheduling, termination, absence of races, or all reactive pipelines.
- Hyper method calls on known collections and hyper prefix/infix operators on
  finite compatible shapes. Unequal shapes, recycling and unknown operands
  remain inconclusive.

Collection callbacks with multi-element batching, dynamic counts, arbitrary
Slip flattening and custom iteration protocols can remain inconclusive. Callback
analysis is limited to 16 nested applications and generic substitution to depth
32. Exceptions from deferred producers are retained for Promise observation;
scheduling, race freedom and termination are not established.

This is a conservative analyzer, not a proof system for arbitrary Raku:

- Predicates outside that allowlist, or predicates depending on unknown
  values, are inconclusive even when nominal types fit. Coercion execution
  remains inconclusive when a conversion is needed.
- Native integer storage follows Raku wrapping semantics: e.g. assigning 300
  to `int8` yields 44, not a type error. That stored constant is used in later
  checks. Floating-point narrowing loses constant precision conservatively.
- Unresolved value-dependent dispatch, dynamic argument flattening, unknown indirect calls, dynamic
  invocants, unsupported AST constructs, and external routines without useful
  return contracts can be inconclusive.
- Collection reads may be missing. Recognized mutation, captured assignments,
  and mutable call arguments invalidate constant-content assumptions while
  retaining declared element/key contracts. Fixed array dimensions, structured
  initialization and constant index bounds are checked; dynamic dimensions or
  indices remain inconclusive. Custom generic parameterizers and complete
  alias/effect analysis remain inconclusive. Reflective changes are not modeled
  as exact contents.
- Runtime subclass dispatch and mutable captured values can require information
  unavailable during compilation. Strict modes intentionally report uncertainty.

The `unverifiable` modes include these limitations; the `mismatch` modes let
inconclusive code compile. The analyzer only examines the explicitly supplied
unit. A dependency can independently opt into checking its own unit.

## Tests

```sh
raku -Ilib t/01-basic.rakutest
prove6 -Ilib t
```

The suite compiles sample programs in subprocesses and checks both diagnostics
and exit status, including precompiled dependencies and non-execution of user
predicates and program mainlines. The primitive compatibility matrix is checked
against Raku's own nominal type checks. [COVERAGE.md](COVERAGE.md) lists the
covered behaviors and the deliberately inconclusive cases; it is not a claim
of exhaustive verification of every possible Raku program.

## Maintaining documentation

Edit `README.md` directly. In `dist.ini`, `[ReadmeFromPod]` has
`enabled = false` so Mi6 builds and releases preserve this documentation.

## Author and license

Fernando Correa de Oliveira <fco@cpan.org>.
Copyright 2026. Artistic License 2.0.

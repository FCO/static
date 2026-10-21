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
`--policy` accepts any of the four policies below. `--/external-signatures` and
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
and the Boolean options `:external-signatures` and `:check-methods` (both default to `True`):

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

Diagnostics contain `[static:mismatch]` or `[static:unverifiable]`, source
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

The no-argument CORE `.pick` and `.roll` on exact built-in lists and arrays retain the
possible element types, including `Nil` when the collection may be empty.
For example, `("bla", 42).pick` or `("bla", 42).roll` can return `Str` or `Int`, so each violates a
declared `--> Int` return contract. Selection is not executed by the analyzer.
Count arguments and custom implementations use normal method analysis.

Simple local `where`/subset predicates are analyzed using primitive constants,
comparisons, arithmetic, Boolean combinations, intervals, type junctions,
`*.chars`, `*.defined`, and known collection lengths. For example:

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
  and exact exception selection/resumption are not proven.
- The elements yielded by `gather`/`take`, values of `start` observed through
  `await` or `.result`, and `supply`/`emit` values checked against inline `tap`
  callback signatures. Mutable captures use declared contracts rather than
  current values; deferred writes invalidate caller assumptions. This does not
  prove scheduling, termination, absence of races, or all reactive pipelines.
- Hyper method calls on known collections and hyper prefix/infix operators on
  finite compatible shapes. Unequal shapes, recycling and unknown operands
  remain inconclusive.

This is a conservative analyzer, not a proof system for arbitrary Raku:

- Predicates outside that allowlist, or predicates depending on unknown
  values, are inconclusive even when nominal types fit. Coercion execution
  remains inconclusive when a conversion is needed.
- Native integer storage follows Raku wrapping semantics: e.g. assigning 300
  to `int8` yields 44, not a type error. That stored constant is used in later
  checks. Floating-point narrowing loses constant precision conservatively.
- Value-dependent dispatch, argument flattening, indirect calls, dynamic
  invocants, unsupported AST constructs, and external routines without useful
  return contracts can be inconclusive.
- Collection reads may be missing. Recognized mutation, captured assignments,
  and mutable call arguments invalidate constant-content assumptions while
  retaining declared element/key contracts. Fixed array dimensions, structured
  initialization and constant index bounds are checked; dynamic dimensions or
  indices remain inconclusive. Nested generic resolution and complete
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

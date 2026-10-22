# Validation coverage

Run `prove6 -Ilib t`. CI runs the suite on Rakudo 2026.09 and latest across
Linux, macOS, and Windows. Local verification is not a substitute for those
platform jobs completing on GitHub.

| Area | Cases exercised | Tests |
| --- | --- | --- |
| Policies and diagnostics | Four warn/fail policies, aggregation, source locations, native SORRY output, structured compiler errors, explicit CU, no runtime execution | `t/01-basic`, `t/07-diagnostics` |
| Returns and flow | `.are`, explicit/implicit exits, nested routines, forward/mutual calls, recursion, shadowing, branch/short-circuit effects, loop widening | `t/02-inference`, `t/06-regressions`, `t/11-state-and-safety` |
| Calls and contracts | Positional/named/optional/slurpy arguments, aliases, arity, captures, methods, private methods, inheritance, roles, `:D`/`:U`, defaults | `t/03-calls`, `t/09-signature-coverage` |
| Method existence | Exact class/instance/primitive receivers, inheritance, broad receivers, FALLBACK, optional dispatch, four policies and opt-out | `t/13-method-existence` |
| Multi and generics | Nominal and constrained specificity, fallback candidates, unresolved constraints, direct `::T` argument/return binding, nested generics | `t/09-signature-coverage` |
| Predicates | Positive/negative cases for parameters, variables, defaults, returns, named arguments, subsets and nested subsets; arithmetic, comparisons, Boolean combinations, intervals, literal constraints, type junctions, primitive string lengths | `t/08-constraints` |
| Collections and state | Typed initialization/reassignment/binding, element writes and insertions, typed hash keys, scalar aliases, missing indices, no-argument CORE pick/roll element alternatives and empty arrays, mutable arguments, captured writes and loss of stale content assumptions | `t/02-inference`, `t/04-collections`, `t/08-constraints`, `t/11-state-and-safety` |
| Nominal types | Concrete Int/Str/Rat/Num/Bool against Int/Str/Rat/Num/Bool/Numeric/Real/Cool/Any/Mu/Int:D/Int:U, compared with Raku's checks | `t/10-type-matrix` |
| Native storage | Nominal rejection, integer narrowing and unsigned wrapping, subsequent predicates on the stored result | `t/05-boundaries`, `t/08-constraints` |
| Unit boundaries | External signatures on/off, missing external returns, external bodies excluded, opted-in module precompilation | `t/05-boundaries`, `t/06-regressions` |
| Bounded/non-executing analysis | No execution of opaque predicates, overloaded comparisons or predicate loops; exponent budget; state reset on analyzer reuse | `t/11-state-and-safety`, `t/12-dynamic-coverage` |
| Containers and effects | Readonly/rw/copy/raw parameters, finite destructuring and nested sub-signatures, immutable/element bindings, fixed array shape and bounds, given arms, exception handlers, deferred captures, gather/start/supply payloads and tap contracts, hyper methods/operators | `t/15-containers-and-effects` |
| CLI | Files/stdin, per-unit isolation, include-path forwarding, repeatable -I/-M, policies, exit status and original source locations | `t/14-cli` |
| Explicit uncertainty | Dynamic destructuring, proxies/raw containers, indirect calls, dynamic symbols/methods, regex constraints, EVAL, virtual/role dispatch, opaque smartmatches, dynamic dimensions/indices and hyper shapes, deferred mutation | `t/09-signature-coverage`, `t/12-dynamic-coverage` |

`t/16-expanded-analysis` covers branch narrowing, integer bounds, dependent
parameter predicates, finite named/positional captures, known indirect calls,
collection callbacks and selection counts, lazy-source and alias invalidation,
closure signatures/captured writes, custom matcher safety, shared removal state, nested generic
contracts, typed handlers, and unreachable-code policies/opt-out. CLI opt-out is
covered in `t/14-cli`. Unreachable diagnostics are an intentional behavior change:
all four policies select them unless `:!check-unreachable` is supplied.

An inconclusive test must pass `fail-on-mismatch` and produce a
`[static:unverifiable]` compilation error under `fail-on-unverifiable`.
Predicates also exercise both warning policies. Unsupported constructs must
not crash the analyzer or be mislabeled as proven nominal incompatibilities.

The safe predicate interpreter is intentionally finite. Arbitrary predicates,
regex semantics, external routine bodies, arbitrary reflective mutation,
complete dependent typing, and the full Raku dispatch/effect system are not
proven by these tests. Newly encountered syntax still needs a regression case.
Raku's own `BEGIN` and other compile-time activity remains normal language
behavior; the analyzer does not suppress it.

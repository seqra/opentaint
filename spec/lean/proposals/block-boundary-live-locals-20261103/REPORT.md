# Boundary live-local proof report

Status: **SELECTED PROPOSAL MODEL**. No implementation, Gradle/analyzer run,
profile, project result or commit is part of this package.

Selected behavior: discard a LocalVar conclusion on an outgoing boundary route
only if instruction liveness proves its incoming old value dead on that route.
On repeat, drop only locals dead on repeat. Live carried values retain the
native path. An AL leaving route uses only its own continuations. This can
remove dead internal summaries/frontier rows; it does not claim equal counts
for those rows. Nonlocal data, whole originals, annotations, completed source/
Target/static effects and observable/live-row behavior are the preservation
scope. No new rule, alias, source permission, field or mark policy is selected.

The constructive Lean model proves:

- finite mask enumeration is complete; the executable intersection of closed
  masks is least and is a fixed point for monotone transfer;
- forward USE/DEF and backward mention/no-kill transfer are monotone;
- any first use before a definite kill is live, and finite first-use paths have
  finite executable search witnesses;
- a dead old-local token has no instruction-read observations along any modeled
  finite execution; dropping it therefore gives equal instruction observations;
- each boundary unions all and only its actual route destinations; dead union
  means every destination is dead;
- producer genuine-leave union followed by actual-route filtering equals the
  actual-route filter alone, so a shared exit cannot leak into a dead branch;
- only LocalVar conclusions are filtered; retained opaque packets, whole
  premises, annotations, nonlocals and already completed effects are unchanged;
- live carried locals remain and dead leaving locals cannot escape.

Finite witnesses cover reset-before-use across feedback, read-before-write,
live carried versus dead AL, the incorrect repeat+leave union and conservative
backward LHS mentions. The solver is deliberately finite and exhaustive. A
polynomial native bitset worklist, its termination/performance bound, instruction
classification and source-index adapter are not kernel-verified.

Native implementation gates remain explicit. Include every real forward/backward
CFG continuation, typed exception/discovery route and canonical exit expansion.
A missing route is not dead. Synthetic/unknown routes must preserve the native
path. A definite DEF must not kill the old LHS on an exception-before-commit
path. Field/array writes do not define their base local. Backward assignment
must retain its LHS mention: the native move microedges reverse differently
from ordinary forward overwrite. Unknown instruction/local classification
keeps the native path, with all relevant locals live.

Instruction-only read/kill extraction must conservatively cover actual native
instruction effects. The operational proof tracks an old conclusion token; it
is not a theorem about arbitrary Kotlin AP transfer, rules, aliases, summary
stores, Targets or reports. No kernel proof assumes these native conclusions
are equal. Future adapter tests must establish observable/live-row projection
preservation for native fixtures (including overwrite, exceptions, branches,
feedback, nested loops, reverse execution, sources/Targets, annotations and
nonlocals). Project quality gates must then check the actual optimization.
The user excluded rule-read and alias analysis; neither is added by this model.

The native extractor must not call `JIRMethodForms.footprint`, which invokes
backward alias expansion. Use a separate pure instruction walker. The backward
CFG must use actual `JIRExitWiredGraph(...).reversed` discovery and preserve
all real canonical exit predecessors; reversing only the ordinary forward edges
is insufficient. Exact source hashes are in `reference-source-pins.json`.

The principal constructive regression is `x = ...; while (...) { tmp = x;
use(tmp); ... }`. The old tmp is dead at the repeat destination because the
next assignment kills it before use. The carried x remains live on repeat.
Tmp stays live inside the body before its use and cannot leave on the AL route.
A boundary-state witness retains the already completed sink/effect value and
the exact x packet while dropping only tmp. No alias/rule special case is used.

Frontend audit traps: `JIRAssignInst.operands` includes both LHS and RHS.
Forward USE must remove a direct local LHS while retaining RHS reads, or the
principal `tmp = x` case will falsely retain tmp. JVM
`LanguageManager.producesExceptionalControlFlow` recognizes explicit throw/exit
forms; false is not a may-throw proof for calls or memory reads. Use the safe
plain-copy DEF cell, or retain the old value when commit is uncertain.

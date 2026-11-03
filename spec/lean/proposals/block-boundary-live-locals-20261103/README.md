# Instruction-only boundary live locals

Status: **SELECTED PROPOSAL MODEL ONLY — no Kotlin implementation**.

```sh
python3 spec/lean/proposals/block-boundary-live-locals-20261103/check.py
```

The finite model computes a least fixed point for each local on a directed
instruction CFG. Forward transfer is `USE || (!DEF && any successor live)`.
Backward transfer is `all instruction mentions || any successor live`; it has
no backward kill. USE includes RHS, receivers, arguments, field/array addresses
and indexes. A plain local assignment can define its LHS after RHS uses. DEF
means a definite committed overwrite on all covered successors. An assignment
that can throw before commit must have no DEF, or use separate read/normal-commit
nodes with exception edges bypassing the commit. Unknown instructions keep all
locals live. No rule-read or alias analysis is introduced.

The reference solver exhausts all finite Boolean masks and intersects all
closed masks. Lean proves enumeration completeness, leastness and the fixed
point. This is an executable proof oracle, not the proposed production bitset
worklist. The transfer is instruction-only; no native summary equivalence is
assumed. First-use-before-kill paths are sound for liveness and yield executable
finite search witnesses. Dead old-local tokens have no instruction-read
observations on any modeled path, including paths that stop before a kill.

A boundary uses only the destinations of its actual directed route. A logical
normal exit can union its genuine leaving routes, then each expanded physical
route filters again. Repeat/feedback has its own mask; it is never borrowed by
the AL exit. The model proves this two-stage filter equals direct actual-route
filtering. Nested loops use the same rule at each route. A live loop-carried
local takes the unchanged native path. There is no live-carried bypass/drop
mechanism in this package.

The filter can discard only a LocalVar conclusion. It retains complete opaque
premises, annotations and nonlocals, and it leaves already completed
source/Target/static effects unchanged. It does not remove input premises,
partial protection, fields, mark memberships, ZERO, STATIC, arguments, receiver,
return, exception or Target values. Filter the conclusion before new summary,
demand or loop-observer work at the selected boundary; already completed effects
remain. Retained packets preserve their first-occurrence order.

Read [REPORT.md](REPORT.md) for the exact proof limits and native gates.

The native extractor must not call `JIRMethodForms.footprint`, which invokes
backward alias expansion. Use a separate pure instruction walker. The backward
CFG must use actual `JIRExitWiredGraph(...).reversed` discovery and preserve
all real canonical exit predecessors; reversing only the ordinary forward edges
is insufficient. Exact source hashes are in `reference-source-pins.json`.

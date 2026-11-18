# Keep EXACT points out of descendant keep guards

15 November 2026. Proposed approach under
[proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
This extends the [exclusion-aware child routing](bidirectional-exclusion-aware-child-replay-20261115.md)
with one point-domain correction. It retains all earlier selected fixes.

**EXACT describes one location during a raw query. An excluded identity keep
strictly below that location must give no result.** Its input guard cannot
match the point. Do not manufacture a MAY descendant from that point.

The [new nested-write example](../reports/bidirectional-nested-write-nontermination-20261115.md)
now stops at **run-3**. All twelve older reference executions are exactly
unchanged. Six new negative/positive references stop at **run-3 through run-11**.
See the [validation and annotated trace](../reports/bidirectional-exact-point-write-progress-20261115.md).

## 1. Semantic change

This is a change to one raw transfer case, not a storage optimization.

An excluded identity keep has this shape, including the same base/path on
both ends and the same FLOW mark:

```text
A.* -> A.* {real field E}, with E nonempty
```

| Operand and guard | Current | Proposed |
|---|---|---|
| `x.$/FLOW` and guard `x.f.*` | Special write-keep exception emits `x.f.MAY/FLOW,D` | No result: guard is strictly below the point |
| `x.$/FLOW` and guard `x.* {f}` | Keep `x.$/FLOW {f}` with the existing layer rules | Same |
| `x.f.$/FLOW` and guard `x.f.* {g}` | Keep the point and real `{g}` | Same |
| STAR, MAY, NE, MUST, or any concrete-mark operand | Existing transfer | Same |
| A value write `y.* -> x.f.g.*` | Prepend the known target fields | Same |

The predicate tests the **current operand leaf**, not its original premise.
It does not discard a whole packed tree because one ancestor is EXACT.
A matching node at the guard, and concrete descendants stored below it, still
use the existing processing.

The restriction is geometric. It needs no instruction-origin tag. It applies
to an excluded identity restriction wherever that native form is used. It
adds no permission to skip call enrollment, boundary rules or write effects.
Calls still use their existing matching and saved-first policy.

Everything else remains unchanged: raw EXACT/STAR admission and priority,
the conditional EXACT/FLOW prefix probe, complete paired C5, field limits,
real exclusions, mark exclusions, protection classes, NORMAL persistence,
normalization, liveness, aliases, statics, rules, and typed ZERO/Targets.
The rule adds no new query, tail kind, evidence label, origin or storage.

## 2. Why this is a domain correction

Consider the ordinary synthetic core form `x.f.g = new Node()`. Its parallel
keeps are:

```text
K0: x.*   -> x.*   {f}
K1: x.f.* -> x.f.* {g}
```

For an EXACT point at x, K0 keeps that point. K1 cannot match it: x is not
inside x.f. Current code has an EXACT/FLOW exception which instead emits
MAY at x.f. A later read can transport this artificial descendant:

```text
current:
    x.$/FLOW,N --K1--> x.f.MAY/FLOW,D --read f--> y.MAY/FLOW,D
proposed:
    x.$/FLOW,N --K1--> no result
```

A plain read already rejects an unknown descendant of EXACT. The proposal
makes the keep restriction follow the same point semantics. It does not
make a stronger claim about an uncertain STAR or MAY operand.

Keep the point's real exclusion from K0. It is needed when the raw complete
FLOW pair later normalizes `$` to `*`. The proposed change must not restore
`x.* -> x.*` without `{f}`.

## 3. Algorithm and native boundary

Use the current traversal and matching information:

```text
applyContribution(rawOperandLeaf, edge):
    if rawOperandLeaf is EXACT/FLOW
       and edge is an excluded identity keep
       and edge.guard is strictly below rawOperandLeaf.path:
        return NO_RESULT

    result = nativeContribution(rawOperandLeaf, edge)
    applyExistingPreparedChildRoutingWhenSupported(result)
    deliverUnmodified(result)
```

This has two distinct justifications:

- **Point rejection:** EXACT cannot match a deeper guard. No child query or
  child-cover test is needed for this rejection.
- **Existing suffix routing:** STAR can match the deeper guard. A coarse
  STAR-to-MAY result may be omitted only with the existing complete prepared
  child service. The previous exclusion-aware rule stays unchanged.

Proposed native edits, for a later implementation:

```kotlin
// Scalar Reference.above:
// EXACT no longer has a write-keep exception.
if (!admitted) return null

// Packed EdgeApplication.flow, at a strict ancestor leaf:
// Before: else if (!exact || writeKeep) ...
else if (!exact) flowHit(...) { /* existing result construction */ }

// Keep exact-node and descendant-tree processing below this branch.
// Delete the now-unused writeKeep classifier/helper.
```

The packed change affects only the ancestor-leaf branch. It must not remove
normal results from matching concrete paths in the same tree. Keep all real
E, mx, marks, H and layers on the results which remain.

When implementation is selected, replace the test-only candidate adapter
with direct production calls. Update the historical component assertions
which deliberately demonstrate the old EXACT-to-MAY result. Keep their
exclusion, normalization and actual-input controls. Add a mixed packed-tree
test with an EXACT ancestor and a relevant matching descendant.

## 4. Why a real descendant still has a route

The initial emission policy already separates the necessary cases.

| Demand and actual | Existing raw family | Effect of the point correction |
|---|---|---|
| `x.MAY`, actual `x.$` | `x.$` | No descendant exists in this point input |
| `x.MAY`, actual `x.MAY` | `x.$` and `x.*` | STAR retains the possible descendants |
| `x.MAY`, actual `x.*` or `x.NE` | `x.*` | No EXACT operand is removed |
| `x.MAY`, actual `x.f.g...` | Bounded first-field `x.f.*`, plus the existing root FLOW point probe | The real input is covered by x.f; the root probe need not invent a descendant |
| `x.MAY`, actual `x.f.$` | `x.f.$`, plus the root FLOW point probe | The point at x.f still matches K1 at its own head |
| MAY/NE with same-head MUST | Dedicated MUST query | Unchanged |

For a concrete word `x.f.s`, the first-field query `x.f.*` covers s without
storing or composing s. A point at x.f still matches the keep at x.f and
retains `{g}`. A point at x never matches that deeper keep.

These are the existing bounded queries, not an additional partition. C2 still
stops after one new field. A cut still emits NE/DEMAND. An input that remains
uncertain still uses ordinary STAR/MAY processing. No exact point is inferred
from missing evidence, and no valid original caller input is suppressed.

The local proof is a point-domain proof. The full reference proofs execute
C2, paired C5 and original-offer replay, including the conditional prefix
probe; they do not assume that initial emission can be bypassed.

## 5. Progress on the new example

With T at x.g, the old backward run-2 renews a root MAY obligation through
its EXACT return probe. The proposed run-2 instead publishes:

```text
NORMAL:
    ret.*   -> x.f.* {f,g}
    ret.f.* -> x.*   {f,g}
DEMAND:
    ret.f.* -> x.f.MAY
    ret.f.* -> x.f.NE
```

The next forward demands are only:

```text
(x.f.MAY | ret.f.*)
(x.f.NE  | ret.f.*)
```

The actual `x.g.MUST/T` does not satisfy either. Saved NORMAL writer/reader
records also cannot return T from this g input. Run-3 emits neither a new
DATA demand nor DemandTarget and stops. The concrete marked g region is
indeed rejected or overwritten before return.

If T is at x.f instead, the field query is relevant. Both the EXACT and MUST
variants retain NORMAL results and stop at run-3. Deeper real f inputs keep
their real cuts and finish at run-5. Thus this is not a repeated-demand
blacklist, a fixed-point timeout or an instruction to drop all MAY work.

## 6. Proofs, cost and limits

The [Lean package](../../spec/lean/proposals/point-write-progress-20261115/README.md)
proves generic point/guard incompatibility, preservation of every retained
native reply, preservation of every native NORMAL keep result, unchanged
non-EXACT/concrete/root keep cases, and a fixed-plan no-extra-work bound.
It also proves all eighteen complete cold executions, independent quiescent
states and handoffs, producer permissions, final observations and natural
DATA plus Target emptiness. The twelve older states are equal at every run.
Earlier selected concrete/MUST cleaner and protection results remain checked
dependencies; their operands are outside the changed case.

Validation: **596 new theorems; 2,083 audited declarations; 105 modules**.
Five native candidate-adapter checks and four original native controls pass.
Production is not patched by these tests.

For a fixed offered fact, query family and native contribution list:

```text
new queries      = old queries
new kept replies ⊆ old native replies
new fixed-plan postprocessing work <= old work
```

No new lookup or evidence store is needed. The existing traversal already
knows the operand tail and whether it is a strict ancestor of the guard.
As with earlier routing, this is not a universal whole-run cardinality bound:
removing a broad MAY can expose smaller members it previously covered.

Scope remains explicit. The new example uses the supported atomic nested-write
**synthetic core form**. No Java-front-end reproduction is claimed. The proof
is not a whole-production simulation or a universal termination theorem.
All supplied reference examples stop without a hard iteration limit.
A 1,000-case nested-write/DAG diagnostic has no new observation regression;
one old/new reference-alignment mismatch remains and is documented in the report.

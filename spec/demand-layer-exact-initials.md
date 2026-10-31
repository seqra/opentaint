# Exact initial facts on the DEMAND layer

Date: 31 October 2026. Status: design for review. Runtime implementation is
unchanged by this document.

This revision specifies the concrete-mark case discussed in the
[conditional-source report](../docs/reports/bidirectional-target-zero-nonzero-source-admission-gap-20261031.md).
FULL mode is the acceptance scope. GROUP stays available with its known
issues. The selected scope is concrete marks only. FLOW keeps its existing
behavior. Section 14 records this decision.

Read this document with [proof-guide.md](proof-guide.md). The executable
proof package is [here](lean/proposals/demand-layer-exact-initials-20261031/README.md).

## 1. Result and semantic scope

The three proposed rules are necessary. They are not sufficient if layer
information is lost on delivery, or if a split sink still emits
NormalTarget. The complete design must include these changes:

| Part | Current behavior | Proposed behavior |
|---|---|---|
| Exact demand with a matching MAY offer | Reject the offer | Admit an exact initial on DEMAND |
| Exact initial from an exact DEMAND offer | The key loses the layer; the start can become NORMAL | Keep DEMAND on the initial edge |
| Entry deduplication | One seen membership per initial key | One membership per key and start layer |
| Weakened run-1 source arm | Can become NORMAL after the FULL layer correction | DEMAND if the arm drops a required origin |
| Weakened run-1 sink arm | Can become NormalTarget after dropping a required origin | DemandTarget plus the full physical sink seed |

These are explicit semantic changes. They are not cache or representation
changes alone. In particular, MAY-to-EXACT admission creates a provisional
point hypothesis; it does not prove definite taint at that point.

Keep the following behavior:

- FULL uses the ordinary computed layer. Do not restore blanket TAINT
  demotion. Keep the independent run-1 static approximation.
- Run-1 still emits singleton origin arms. Later forward runs keep their
  complete ND premises and same-call joins.
- Keep base, mark, path, exclusion, field-budget, and static-anchor guards.
- Keep summary intersection paired. Do not combine entry permission from
  one row with exit permission from another row.
- Keep persisted summary application before the current demand gate.
- Keep NormalTarget's normal-only application and backward exclusion.
- Keep Target outside AP facts, initial keys, and AP mark sets.
- Keep explicit ZERO admission, source permissions, static composition,
  report IDs, and completed-barrier publication.
- Keep the selected absence of END effects.

No runtime change, new propagation service, added-fact store, or grounding
support label is part of this document.

## 2. Terms and types

`N` means NORMAL. `D` means DEMAND. `$` means EXACT, `*` means STAR,
`[any]` means MAY, and `[any-taint]` means MUST.

An exact *location* and a definite *result* are different properties:

```text
p.$/T, N : definite T at the exact point, in the current abstract analysis
p.$/T, D : a provisional exact-point requirement or result
```

In a backward run, a NORMAL exact fact is an exact requirement. It is not
proof that the caller already has that taint in the forward execution.

Keep the layer outside the initial key:

```kotlin
data class AdmittedInitial(
    val initial: InitialAp,
    val layer: Layer,
)

// InitialAp interning, equality, and hashing do not change.
// AdmittedInitial equality includes the layer.
```

An `AdmittedInitial` is an entry command. It is not an edge premise, a
source permission, or a new Target type. The premise of its initial edge
is the existing InitialAp.

Demand rows are guidance. Their origin in a prior DEMAND edge is not a
lower bound on the next starting layer. A NORMAL ND edge can also produce
guidance under the existing handoff rule. Do not make either kind of
guidance force every later analysis to DEMAND.

## 3. Exact admission

Let `d = p.$/T` be a well-formed exact demand. Let `a` be the actual
submitted fact after the existing input cut. Use full concrete marks.

First apply the existing guards:

```text
same base
compatible required and actual marks
both paths fit the current field limit; limit >= 1
legal actual fact and initial shape
the actual location covers the requested point
actual exclusions admit descent to the requested point
```

An exact concrete demand has an empty field exclusion. Reject an invalid
exact demand with nonempty exclusion. Do not erase actual exclusions.
The existing demand-side FLOW exclusion normalization is a separate rule.

Then emit the requested point, with its selected layer:

| Exact demand | Submitted fact | Initial edge |
|---|---|---|
| `p.$/T` | `p.$/T, N` | `p.$/T -> p.$/T, N` |
| `p.$/T` | `p.$/T, D` | `p.$/T -> p.$/T, D` |
| `p.$/T` | `p.[any]/T, D` | `p.$/T -> p.$/T, D` |
| `p.f.$/T` | `p.[any]/T, D` | `p.f.$/T -> p.f.$/T, D` |
| `p.f.$/T` | `p.[any-taint]/T, N`, with admitted `f` | `p.f.$/T -> p.f.$/T, N` |
| `p.f.$/T` | `p.[any-taint]/T, N`, excluding `f` | None |
| `p.$/T` | `p.f.$/T` or `p.f.[any]/T` | None |
| `p.f.$/T` | `p.g.[any]/T`, `f != g` | None |
| `p.$/T` | Any fact with concrete `U != T` | None |
| `p.$/T` | Abstract FLOW with no concrete T witness | None |

The MAY case also applies when the actual MAY prefix is a strict ancestor
of the requested point. The result uses the *requested* path. It does not
move the request to an unrelated actual child.

Do not use symmetric geometric overlap. A fact below an exact requested
parent cannot prove or provisionally supply that parent under this rule.
All other pre-existing tail cells keep their current geometric policy.
Exact emission in those cells must also retain an actual DEMAND layer.

For the changed exact cell:

```kotlin
fun exactAdmission(d: Pattern, actual: FactsLeaf): AdmittedInitial? {
    if (!existingExactGuards(d, actual)) return null
    val loss = if (actual.tail == ANY) DEMAND else NORMAL
    return AdmittedInitial(exactKeyAt(d), actual.layer or loss)
}

// The demand row's prior layer is deliberately not an operand.
```

Even an invalid NORMAL MAY header must not turn this coercion into a
NORMAL proof. The MAY-to-EXACT cell explicitly selects DEMAND. Production
MAY inputs must still satisfy the existing well-formedness rules.

## 4. Start edges and ordinary operations

The start must preserve the admitted uncertainty:

```kotlin
fun canonicalAdmission(initial: InitialAp, supplied: Layer): AdmittedInitial =
    AdmittedInitial(initial, intrinsicStartLayer(initial) or supplied)

fun start(seed: AdmittedInitial): Facts {
    val intrinsic = startFact(seed.initial)
    return intrinsic.withLayer(intrinsic.layer or seed.layer)
}
```

For exact concrete keys, the intrinsic layer is NORMAL. Thus an admitted
exact DEMAND key starts as an exact DEMAND identity. A concrete STAR key
still starts DEMAND under the ordinary AP rule. This proposal does not
promote STAR, MAY, field cuts, or cleaner losses to NORMAL.

Canonicalize the descriptor before coverage checks and deduplication.
For example, a proposed `(concrete STAR,N)` and `(concrete STAR,D)` both
start in D. They must be one actual admission lane, not a fictitious N
membership followed by duplicate D work. Apply the existing mode/static
policy at its existing boundary as well; do not create a NORMAL lane that
the selected starting policy always demotes.

Apply the same layer preservation to exact run-1 concrete request answers.
An exact incoming `p.$/T, D` must not become a NORMAL request answer merely
because its canonical key has `$`. The run-1 abstract STAR/FLOW policy seed
remains its existing policy abstraction; do not make it inherit every
concrete supplier's layer as an unrelated change.

A dependent operation joins the layers of its required inputs and its
own approximation. It cannot turn a DEMAND derivation into NORMAL by
copying an exact tail, applying a NORMAL summary, or assigning another
mark. An independent ZERO GEN retains its separate existing semantics.

## 5. Two admission memberships per key

The entry store must distinguish `(I,N)` and `(I,D)`:

```kotlin
class InitialFactStore {
    // Two seen bits per existing InitialAp; no new fact index.
    fun add(seed: AdmittedInitial): Boolean
}
```

| Arrival order | Required processing |
|---|---|
| D, then the same D | Start D once |
| N, then the same N | Start N once |
| D, then N | Start both; N is a later definite analysis |
| N, then D | Start both; D can produce needed DemandTarget guidance |

NORMAL must not suppress DEMAND here. Consider `check(p) { sinkT(p); }`.
A NORMAL admission can produce `I -> NormalTarget(id)`. A weak caller
cannot apply that NormalTarget, and backward analysis ignores it. If a
later DEMAND admission of the same key is discarded, no DemandTarget is
produced for the weak caller. The report rule would stay safe, but its
required continuation would be lost.

Do not add cross-layer admission subsumption in this revision. Pending
jobs must not be erased when the other layer arrives. Existing post-
statement stores retain their layer-aware deduplication.

The same rule applies to per-origin source-result admission bookkeeping:
if an arm first has DEMAND support and later has complete NORMAL support,
its old origin-only seen flag must not hide the NORMAL result. Keep
existing protection annotations monotone within each result lane.

## 6. Caller handling

Keep the selected call order:

```text
1. Apply persisted summaries to the original submitted facts.
2. Query current demand and obtain layered admitted initials.
3. If none exist, skip the current callee subscription/start.
4. Otherwise register the existing subscription and deliver those seeds.
```

The caller passes the lookup result to the callee. The callee does not
repeat C2. Carry the descriptor through messages and request-answer batches.

Keep the original submitted Facts in the subscription. Do not replace a
submitted MAY fact by the canonical exact hypothesis. The existing summary
and Target matcher selects the relevant actual input. Its layer, the
caller layer, and the link layer remain part of application support.

A NORMAL AP summary can apply to a DEMAND offer and yield a DEMAND result.
A NormalTarget cannot do so: it is rejected on non-NORMAL support. It is
not converted to DemandTarget. The separate DEMAND callee execution must
produce its own anonymous terminal.

Admission is not a source hit. Record source/action permission only when
the existing reverse action actually executes. Keep native replay separate
from actual GEN callbacks.

## 7. C2 and C5 use one image

Keep the invariant:

```text
C5 may retain an initial geometry A under Dc
only if C2 can emit A from some legal actual input under Dc.
```

The layer-aware form also has a constructive witness. For an admissible
exact key and either layer L, use the canonical exact actual fact at that
key with layer L. C2 emits the same `(key,L)`.

The new MAY rule supplies an additional DEMAND witness for an already
legal exact key. It does not justify admitting arbitrary overlapping keys.
For concrete exact demands, the structural key image is unchanged; the
actual-input route and layer preservation change.

Keep C5's entry-image validation and ordinary exit intersection. Preserve
the raw result layer. Intersecting an exact DEMAND result must not create
a NORMAL summary. The stored premise stays the unchanged InitialAp or
ordinary later ND premise; there is no layer in premise identity.

## 8. Cause-specific DEMAND for run-1 premise weakening

Wait for the complete source or sink condition before projecting origins.
The layer of each projected arm must account for the premises it drops.

For one complete abstract witness, remove ZERO dependencies and find its
distinct input origins:

```text
All inputs NORMAL and only origin P plus optional ZERO:
    P retains the complete support; its arm can be NORMAL.

Distinct required origins P and Q, projected separately:
    P -> result is DEMAND; Q -> result is DEMAND.

Any required input DEMAND:
    dependent arms are DEMAND.

Complete all-ZERO witness:
    ZERO arm is permitted, with the joined witness layer.

No complete witness:
    emit no arm and no ZERO shortcut.
```

For factored origin domains, an arm P can retain NORMAL only if one
complete NORMAL binding can choose P or ZERO in every required column.
This can be tested by membership in the existing origin domains. It does
not require enumeration of origin products or a grounding label on edges.
A conservative implementation may demote additional arms, but must not
declare a dropped dependency complete.

This is separate from ordinary FULL transfer. A unary FULL edge with
definite exact evidence stays NORMAL. A split two-origin arm is DEMAND
because its premise has lost support, even if its conclusion is exact.

Apply the rule to both data and terminal results:

```text
Complete witness: {P/T1, Q/T2} -> ret.$/U, N
Run-1 projection: P/T1 -> ret.$/U, D
                 Q/T2 -> ret.$/U, D

Complete sink witness: {P/T1, Q/T2}
Run-1 projection: P/T1 -> DemandTarget
                 Q/T2 -> DemandTarget
```

Do not emit unary NormalTargets from this weakened sink witness. Retain
the existing full physical sink seed, including the complete predicate.
Seeding only one projected literal would lose the later conjunction.

Later forward runs keep the existing complete ND summary and same-call
join. This proposal does not reintroduce ND executable edges in run-1.

## 9. Principal model trace: source condition

```java
// Sources A and B assign T1 and T2 at their results.
// Producer: CM(p,T1) AND CM(q,T2) -> assign U to ret.$.
// Sink: CM(value,U).
Object make(Object p, Object q) { return configuredProducer(p, q); }

void main() {
    Object a = sourceA();
    Object b = sourceB();
    Object r = make(a, b);
    Box z = new Box(); z.g = r;
    Box y = new Box(); y.f = z;
    Object bad = make(a, new Object());
    sinkU(y.f.g); // required positive
    sinkU(bad);   // required negative
}
```

Proposed run-1, forward, field limit 1:

```text
make exact initials: p.$/T1 N, q.$/T2 N
local condition: complete
projected summaries: p.$/T1 -> ret.$/U D
                     q.$/T2 -> ret.$/U D
good call result: r.$/U D; after writes: y.f.[any]/U D
bad call result: provisional bad.$/U D
both provisional sink hits: DemandTarget, with their full sink seeds
no NormalTarget from either weakened result
```

Proposed run-2, backward, field limit 1:

```text
good-call offer: ret.[any]/U D
exact guide: ret.$/U
admission: ret.$/U D -> ret.$/U D

bad-call offer: ret.$/U N
same key can also be admitted in NORMAL
both admission lanes are processed

reverse MULTI action: recover both p/T1 and q/T2 requirements in DEMAND
good caller maps them to a/T1 and b/T2
actual reverse source actions retain the required forward permissions
no permission is manufactured by admission alone
```

The backward bad-call offer is N because the existing physical sink seed
asks for that exact point under the admitted NORMAL ZERO control. It is
not a copy of the provisional forward bad result. The good physical seed
is also initially exact, but its reversed field path is cut to MAY/D.

Proposed run-3, forward, field limit 2:

```text
actual a/T1 and b/T2: exact NORMAL
guidance came from DEMAND; starting layer is nevertheless NORMAL
make uses its ordinary complete ND summary
good call satisfies both inputs -> U N -> root NormalTarget(good)
bad call lacks T2 -> no U -> no NormalTarget(bad)
```

The model proves the required report by run-3 and absence of the negative
report. It does not prove that the whole driver stops at run-3. Existing
NORMAL ND guidance can require further iterations.

The current measured implementation has not been changed to this design.
Its latest trace completes run-3 and reports both sinks through NORMAL
split arms. Do not present the proposed model trace as a new JVM result.

## 10. Direct ND sink and mixed-layer Target cases

```java
void check(Object p, Object q) {
    sinkWhen(CM(p,T1) && CM(q,T2));
}
void main() {
    Object a = sourceA(), b = sourceB();
    check(a, clean);
    check(clean, b);
}
```

Shared run-1 method analysis can contain both hypothetical exact inputs.
Its projected sink arms must be DemandTarget. Two incomplete callers must
not each apply a unary NormalTarget. The later full predicate and same-call
binding keep both calls negative. The new exact-admission rule cannot undo
a false NormalTarget already persisted in run-1.

For `check(p) { sinkT(p); }`, one definite caller and one MAY caller can
admit the same exact key in N and D. Both lanes are required. N produces
NormalTarget; D produces DemandTarget and its sink seed. Keep retained
NORMAL-key deduplication independent from the DEMAND lane and source/sink
seed membership.

An anonymous DemandTarget may conservatively reach more callers than the
one that first caused its DEMAND analysis. Do not suppress it merely
because some NormalTarget exists for that initial. They can cover different
sinks. This revision does not add terminal IDs or cross-layer subsumption.

## 11. Existing Target and ZERO machinery

Keep these rules without a new terminal service:

| Operation | Rule |
|---|---|
| Sink with complete NORMAL support and retained dependencies | NormalTarget with the existing report ID |
| Sink with DEMAND support or weakened dependencies | DemandTarget plus full physical seed |
| NormalTarget application | Complete NORMAL caller, selected input, and link support only |
| NormalTarget in backward analysis | Ignore |
| Actual reverse source completion | DemandTarget under the existing full original premise |
| Terminal C5 | Same complete paired demand, using the existing ZERO-exit query |
| Run-1 static terminal composition | Existing lazy typed Target completion |
| Final report | Configured-root ZERO-to-NormalTarget rows only |

There is no Target initial. MAY data cannot become ZERO. ZERO retains the
existing explicit control admission and existing ZERO starting policy;
its AP encoding as an exact special value is not a data-point coercion.
Normal configured-root starts remain NORMAL. This revision does not select
a new ZERO-layer policy.

An exact DEMAND data seed has a nonzero original. Dependent transfer keeps
that original; backward source completion produces a terminal under it.
It does not open a ZERO-only call path. Independent existing ZERO GEN
and control paths remain outside this new data coercion.

At a caller, use its existing CallerRef original. This can restore an
already admitted ZERO caller context. It does not construct ZERO from
the data shape or add a fallback ZERO entry permission.

Do not persist a DEMAND data summary as a NORMAL native record. A NORMAL
summary derived from a separate definite admission can still be reused,
subject to the actual caller-support rules above.

## 12. Termination and work bounds

For a fixed finite set of initial keys, entry admission adds at most two
memberships per key. Same-layer duplicate offers add no work. The actor
still uses the existing post-statement edge deduplication and protocol.

This does not imply convergence across iterations. For example:

```java
// opaqueMay has a pass to ret.[any], in every field limit.
void main() { Object x = sourceT(); Object y = opaqueMay(x); sinkT(y); }
```

An intrinsic MAY output can supply the same provisional exact DEMAND
initial in every iteration. Its sink produces DemandTarget each time.
Increasing the field limit adds no missing path information in this case.
The proof model constructs this repeated frontier with finite work per
round and no NormalTarget.

Keep the existing timeout and iteration policy. Do not stop merely because
counts are equal, promote the point to NORMAL, or invent a source hit to
force convergence. Selecting a progress rule or suppressing already settled
sink work would be a separate design.

## 13. Implementation boundaries and verification

After review, a runtime implementation must carry the descriptor through:

```text
restricted C2 emitter and result/coverage accumulator
DemandStore.initials and emitRestrictedInitials
caller-provided admission result and runner initial messages
InitialFactStore and actor start
run-1 concrete request-answer accumulator and answer messages
```

No new index is required. Do not put Layer in InitialAp or change ND member
identity. A two-bit entry map and descriptor sets are sufficient. Fully
covered lookup must account for the needed descriptors, not only shape.

Source and sink rule owners must classify weakened arms before publication.
Do not teach MethodEdgeStore to infer rule support or add GroundingSupport.
The rule owner's existing complete witness/origin domains supply the test.

Required runtime checks include:

- Same-path and ancestor MAY admission in D; exact D stays D; later exact N
  starts N. Reject wrong bases, marks, descendants, siblings, and budgets.
- Actual field exclusion blocks descent. Exact concrete demand E is empty.
- Both admission orders process N and D once; duplicates create no work.
- Caller subscriptions keep actual facts. NORMAL cached Targets reject D.
- Source and direct sink ND splitting emits no false NormalTarget.
- Full physical predicate seeds and real source-action IDs survive.
- The proposed source and direct-ND-sink examples reach the stated results.
- Native record and static C5 tests keep their existing behavior.
- An intrinsic MAY case remains provisional; no general termination claim.

The Lean package proves arbitrary-path exact admission guards, layer
preservation, constructive C2/C5 image witnesses, admission deduplication,
source/sink origin projection, Target layer rules, the principal pipeline,
and the non-convergence counterexample. Its README states the adapter
obligations and limits. The models do not verify the Kotlin implementation.

## 14. Concrete marks only

The user selected concrete marks only for this revision. The new exact
DEMAND admission rule does not apply to FLOW.
The current runtime widens some exact DEMAND FLOW facts to MAY. It also
normalizes FLOW summary `$` to `*`, and restricts later FLOW demand shapes.

Keep these FLOW rules, including its transfer, C5, and handoff rules.
An extension to FLOW needs a separate design and proofs. It is deferred.

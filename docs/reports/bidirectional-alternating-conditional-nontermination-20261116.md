# Alternating conditional generators: an acyclic demand cycle

16 November 2026. Synthetic data-flow reachability. FULL marks. No production
change. **Historical counterexample:** NORMAL uniform actual DATA coverage
now resolves this case at **run-5** in the selected reference. Its Target
model retains all already-emitted effects. See the
[repair and checked cold trace](bidirectional-normal-uniform-actual-coverage-20261116.md).

This is a counterexample to the earlier
[consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md),
including NE, prepared children, concrete FLOW backing, definite saved-MUST
reads and definite EXACT/MUST reply support.

**Result:** the same two cross-mark demand relations recur at every forward
handoff. The proof has no iteration bound. The unchanged native core also
completes **run-31** with an outgoing root DemandTarget in every run. That
finite native capture is a compatibility check, not the non-termination proof.

## 1. Code and rules

```java
class Box { Box f; Box g; }

Box make(Box p) {
    Box r = new Box();
    // A: CM(p.f.g.MAY, T) => assign U to r.MUST.
    // B: CM(p.MAY,     T) => assign U to r.f.MUST.
    // C: CM(p.f.g.MAY, U) => assign T to r.MUST.
    // D: CM(p.MAY,     U) => assign T to r.f.MUST.
    return r;
}

void root(Box a) {
    // Entry producer: a.f.MUST/T, NORMAL.
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observation: CM(z.MAY, U).
}
```

A–D are four unary conditional marking actions at the same statement. They
write to the fresh `r`, not to `p`. Each action generates a new full mark;
it copies neither the input object nor its field suffix. In particular,
none is a pass rule. Every configured target is MUST, never intrinsic MAY.
MAY arises from ordinary AP application to an unknown field suffix.

Both CFGs are straight-line. The call graph has the single arc `root → make`.
Calling `make` three times is not recursion. There are no cleaners, loops,
statics, aliases, unresolved bodies, ND rules or externally supplied MAYs.
Only marking and observation rules supplement ordinary analyzed code.

Use limits `1,1,2,3,...`, without a hard iteration limit. All E/mx are empty
and all relevant H memberships are plain. `make` changes T to U or U to T,
so it never restores its own original input mark. The original premise in
`root` is ZERO, including across all three calls. No protection flag is used
to keep the cycle alive.

## 2. Notation and scope of the trace

```text
M = MAY; NE = non-empty MAY; MUST = uniform taint; $ = EXACT; * = STAR
N/D = NORMAL/DEMAND; Z = ZERO; DT = DemandTarget; NT = NormalTarget(id)
[Dc | Dp] = one entry demand with its own paired output selector
flip(T)=U; flip(U)=T; m ranges over {T,U}

F_m = p.*/m       -> ret.M/flip(m), D
B_m = ret.*/flip(m) -> p.M/m,       D
Ff  = p.f.*/T     -> ret.M/U,      D
J_m = ret.*/flip(m) -> p.f.NE/m,    D

forward entry row from B_m: [p.M/m | ret.*/flip(m)]
backward entry row from F_m: [ret.M/flip(m) | p.*/m]
```

The annotations show the **mandatory witness projection**, not a claim that
all other owner state is empty. This is sufficient for non-termination only
because the proof quantifies over additional admitted summaries and complete
ready reply packets at every run. It proves that they cannot remove the
listed root MAY/DEMAND witnesses. The finer `J_m` rows are shown explicitly;
the proof does not disable them or assume that NORMAL analysis fails.

For an exact list of the base initial commands in the trace, use these
families. FLOW companions remain independent queries:

```text
C2([p.M/m], p.M/m,D) = {p.$/m,D; p.*/m,D; p.*/FLOW,N}
C2([p.M/T], p.f.MUST/T,N)
    = {p.f.*/T,D; p.f.*/FLOW,N; p.$/FLOW,N}
C2([p.f.NE/m], p.f.MUST/m,N) = {p.f.MUST/m,N}
C2([p.f.NE/m], p.MUST/m,N)   = {p.f.MUST/m,N}

C2([ret.M/m], ret.M/m,D)
    = {ret.$/m,D; ret.*/m,D; ret.*/FLOW,N}
```

Prepared children extend these sets with the existing one-level family at
observed qualified heads. They do not cancel an existing concrete STAR
start. The delegated unknown-field rule applies to correlated FLOW reads;
it does not suppress these concrete mark-changing GEN actions.

## 3. The two native transfer steps

For each input mark `m`, rule A or C has this selected input and target:

```text
p.f.g.M/m -> r.MUST/flip(m)
```

Its application to `p.*/m,D` or `p.f.*/m,D` must read an unknown field.
It produces `r.M/flip(m),D`, then the ordinary return gives `ret.M/flip(m),D`.
No field is cut to produce that root MAY. Rule B or D also produces the
separate `ret.f.MUST/flip(m),D`. Same-layer MAY union can absorb this second
executable result; retaining it as qualified guidance does not remove MAY.

Backward, the action target `r.f.MUST/flip(m)` is read by `ret.*/flip(m),D`.
Its ordinary reversed application reaches `p.M/m,D`. The other action gives
`p.f.g.M/m,D`. Its real global/relative cut gives `p.f.NE/m,D`.
Thus the same backward query produces both `B_m` and the finer `J_m`.

This is the essential switch: the forward coarse result uses A/C; the
backward coarse result uses B/D. More field budget does not force these two
witnesses to stay on the same action.

## 4. Run-1, forward, limit 1

```java
// root demand: unrestricted run-1.
// submitted: Z. Initial: Z -> Z,N.
void root(Box a) {
    // Entry producer: Z -> a.f.MUST/T,N.
    Box x = make(a);   // offer p.f.MUST/T,N; obtain x.M/U,D.
    Box y = make(x);   // offer p.M/U,D;      obtain y.M/T,D.
    Box z = make(y);   // offer p.M/T,D;      obtain z.M/U,D.
    // Observation produces Z -> DT,D.
}
// Published root: Z -> DT,D.

// make demand: unrestricted run-1.
// submitted: p.f.MUST/T,N; p.M/U,D; p.M/T,D.
// Relevant run-1 mark-request starts: p.*/T,D; p.*/U,D.
// Their FLOW starts and unchanged argument/Z identities remain ordinary.
Box make(Box p) {
    Box r = new Box();
    // A,B,C,D as declared above.
    return r;
}
// Published marked witnesses: F_T; F_U.
// Other action result before same-layer union: p.*/m -> ret.f.MUST/flip(m),D.
```

Handoff includes `[ret.M/flip(m) | p.*/m]` for both marks and the root
`[Target | Z]` control pair. No marked DATA row has been planted at run-3.
The cold bootstrap is the direct generation of these run-1 relations.

## 5. Run-2, backward, limit 1

Backward annotations place published summaries above each declaration and
entry demand, actual offers and initials after its end.

```java
// Published root: Z -> DT,D; real producer permission renewed.
void root(Box a) {
    // Entry producer: backward a.M/T,D meets a.f.MUST/T.
    Box x = make(a);   // backward x.M/U,D -> a.M/T,D.
    Box y = make(x);   // backward y.M/T,D -> x.M/U,D.
    Box z = make(y);   // backward z.M/U,D -> y.M/T,D.
    // Reverse observation starts z.M/U,D.
}
// root demand: [Target | Z]. Submitted ZERO at its reverse boundary.
// Initial: Z -> Z. The actual producer hit yields Z -> DT,D.

// Published make: B_T; B_U; J_T; J_U.
// The ret.$ queries can also publish ret.$/flip(m) -> p.f.NE/m,D.
Box make(Box p) {
    Box r = new Box();
    // Reverse each A,B,C,D action at its own original target.
    return r;
}
// Demand: [ret.M/U | p.*/T]; [ret.M/T | p.*/U].
// Submitted in reverse call order: ret.M/U,D; ret.M/T,D; ret.M/U,D.
// Initials per offered mark: ret.$/m,D; ret.*/m,D; ret.*/FLOW,N.
```

`J_m` is retained as a qualified finer row before executable root-MAY union.
The handoff therefore contains both the coarse forward rows
`[p.M/m | ret.*/flip(m)]` and fine rows
`[p.f.NE/m | ret.*/flip(m)]`, plus the corresponding exact-return rows.
Discarding the finer rows is not a premise of this counterexample.

## 6. Run-3, forward, limit 2

```java
// root demand: [Target | Z]. Submitted Z. Initial Z -> Z.
void root(Box a) {
    // Entry producer supplies a.f.MUST/T,N again.
    Box x = make(a);   // Coarse reply x.M/U,D remains.
    Box y = make(x);   // Its coarse offer gives y.M/T,D.
    Box z = make(y);   // Its coarse offer gives z.M/U,D.
    // The MAY/D witness produces Z -> DT,D again.
    // Finer uniform replies can independently reach the NORMAL observation.
}
// Published root includes Z -> DT,D; any NORMAL report is separate.

// make coarse demand: [p.M/T | ret.*/U]; [p.M/U | ret.*/T].
// make fine demand: [p.f.NE/m | ret.*/flip(m)] and exact-return partners.
// Mandatory coarse offers: p.f.MUST/T,N; p.M/U,D; p.M/T,D.
// Coarse initials: p.f.*/T,D; p.*/U,D; p.*/T,D,
//                 plus the exact/structural companions listed in section 2.
// Fine uniform offer p.f.MUST/m,N starts p.f.MUST/m,N.
// An independent root-MUST offer also starts that same fine MUST query.
Box make(Box p) {
    Box r = new Box();
    // A,B,C,D unchanged.
    return r;
}
// Published coarse witnesses: Ff; F_U; F_T.
// Fine query can publish p.f.MUST/m -> ret.MUST/flip(m),N,
// and the paired exact-return version. This does not erase F_T or F_U.
```

This is not a claim that NORMAL output is unavailable. From the fine first
query, a NORMAL uniform U reply can supply a uniform T reply at the second
call and uniform U at the third. The generic proof allows even more NORMAL
replies than this. Selected cross-layer support absorbs identical concrete
EXACT/MUST values only; it does not absorb a MAY/D value under a MUST/N one.

## 7. Run-4 and every later backward run

```java
// Published root includes Z -> DT,D; producer permission renewed.
void root(Box a) {
    // Entry producer is reached by a.M/T,D.
    Box x = make(a);   // x.M/U,D -> a.M/T,D.
    Box y = make(x);   // y.M/T,D -> x.M/U,D.
    Box z = make(y);   // z.M/U,D -> y.M/T,D.
    // Reverse observation starts z.M/U,D.
}
// Demand: [Target | Z]. Submitted/initial ZERO as in run-2.

// Published make includes B_T; B_U; J_T; J_U.
Box make(Box p) {
    Box r = new Box();
    // A,B,C,D reversed as usual.
    return r;
}
// Demand includes [ret.M/flip(m) | p.*/m], from F_m.
// It also includes [ret.M/U | p.f.*/T], from Ff, and qualified extra rows.
// Submitted: ret.M/U,D; ret.M/T,D; ret.M/U,D, plus ready precise replies.
// Mandatory initials: ret.*/U,D; ret.*/T,D.
// Their ret.$ and FLOW companions remain present as in section 2.
```

For the coarse row, its own Dp has zero fields, so C5 still cuts the other
`p.f.g.M/m` output to `p.f.NE/m`, even when the global limit exceeds two.
This fine cut is additional work. It is **not needed** to regenerate `B_m`:
that relation already has root `p.M/m` before any cut.

## 8. Run-5 and every later forward run

The run-3 forward annotation applies verbatim with the larger global limit.
The critical C2 and C5 cells do not depend on that limit:

```text
[p.M/m | ret.*/flip(m)] + offered p.M/m,D
    C2: p.*/m -> p.*/m,D
    A/C unknown-field action: p.*/m -> ret.M/flip(m),D
    C5 raw entry: accepts the actual C2 start
    C5 output: keeps root MAY, with FL=0 and own budget min(limit,1)
    handoff: [ret.M/flip(m) | p.*/m]

[ret.M/flip(m) | p.*/m] + offered ret.M/flip(m),D
    C2: ret.*/flip(m) -> ret.*/flip(m),D
    B/D reverse action: ret.*/flip(m) -> p.M/m,D
    C5 raw entry: accepts the actual C2 start
    C5 output: keeps root MAY, with FL=0 and own budget min(limit,1)
    handoff: [p.M/m | ret.*/flip(m)]
```

The three-call offer chain is `a.f.MUST/T,N → x.M/U,D → y.M/T,D → z.M/U,D`.
The reverse chain is `z.M/U,D → y.M/T,D → x.M/U,D → a.M/T,D`.
Every fact starts at a code base. No field name is used as a base.

## 9. Why the selected rules do not stop the cycle

| Existing rule | Why the recurring witness remains |
|---|---|
| Real cuts emit NE | Root MAY here comes from an unknown-field action, not a cut. Its field length is zero. |
| Prepared children and qualified heads | They add finer starts. Base concrete STAR is retained. GEN is outside correlated FLOW delegation. |
| FLOW backing, including DEMAND FLOW | Covers a diagonal `m→m` membership. These relations change `m→flip(m)`. Native arrival-order tests check this distinction. |
| NORMAL uniform provider covers NE | The witness has STAR premise and MAY output and is cross-mark. All three guards exclude it. |
| Definite saved-MUST replay | The mandatory witness uses a **current STAR** relation. No provisional saved-MUST lane is used. |
| EXACT/MUST reply support | Root MAY/D is ineligible, even beside NORMAL uniform replies. |
| Same-layer MAY/MUST canonicalization | It can remove smaller results under root MAY/D, not the root MAY/D itself. |
| Handoff R1/R2/R4 | Critical premise is STAR, conclusion is MAY, and no ND exists. |
| Handoff R3 | Root MAY is already the broadest same-premise conclusion. Deduplication retains a final witness for its row. |
| NORMAL report persistence | A NORMAL report does not cancel an independent DemandTarget or its DATA guidance. |

Deleting one arbitrary action-specific route without a coverage proof is not
part of the approach. No such extra repair is assumed here.

## 10. Uncapped proof

[Alternating.lean](../../spec/lean/proposals/alternating-condition-cycle-20261116/Alternating.lean)
imports the existing non-empty-MAY C2 and paired raw C5 functions. The proof
is a **witness-projected simulation**, not an equality claim for the full
engine state:

1. Construct the cold run-1 witnesses with the actual marking transfer.
2. Use the inherited C2 and C5 to prove each critical forward/backward
   relation exists for **every positive global field limit**.
3. Prove its ordinary current STAR application produces the next actual
   offer in the three-call chain. All three offers are reached; none is
   supplied as an external intrinsic-MAY value.
4. Prove root MAY/D survives canonicalization with **arbitrary extra ready
   replies and admitted summaries**. Children are additive and the selected
   rules in section 9 cannot remove these cross-mark witnesses.
5. Reverse/pair the admitted relations normally. Prove by induction that
   the corresponding two rows occur at every odd/even handoff, with arbitrary
   additional admitted summary history at every step.
6. Check the existing root ZERO/Target paired restriction, reverse producer
   hit, source permission and ZERO restart. Thus the route is not starved
   on a later run.

In equations, for all `n ≥ 0`, with no finite cutoff:

```text
{[ret.M/U | p.*/T], [ret.M/T | p.*/U]} ⊆ demandAfter(2n+1)
{[p.M/T | ret.*/U], [p.M/U | ret.*/T]} ⊆ demandAfter(2n+2)
root has an actual Z -> DT witness in the corresponding control closure.
```

Therefore the outgoing refinement frontier is never empty. Increasing the
limit cannot change the two root-MAY transfers. The analyzer does not stop
under its selected uncapped empty-demand policy. This is an iteration cycle
of the analysis, not a cycle in the analyzed program.

The model covers this plain, empty-exclusion, FULL, unary, acyclic scope.
Native tests check both GEN outputs and cross-mark storage. It is not a
whole-engine bisimulation or a measurement of an integrated NE implementation.
The consolidated proposal is not yet integrated, so native and proposal
traces must remain distinct.

## 11. Validation and reproduction

[Proof package](../../spec/lean/proposals/alternating-condition-cycle-20261116/README.md)
and [native test](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/AlternatingConditionalCycleTest.kt).

```bash
python3 spec/lean/proposals/alternating-condition-cycle-20261116/check.py \
  --out /tmp/alternating-condition-proof
cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.AlternatingConditionalCycleTest
```

Validation: **42 new constructive claims; 2,437 audited claims in 122 modules**.
Only `propext` and `Quot.sound` occur in the new theorem audit.

Native: **3 new tests and 7 definite-MUST control tests pass**. The driver test completes **run-31**, policy stop,
with root DemandTarget in all 31 runs and zero NORMAL reports in unchanged
production. It checks no integrated proposal completion. The other tests
cover eight native GEN applications and both arrival orders of diagonal
versus cross-mark FLOW coverage.

The finite native marked summaries are:

| Native completed run | `make` cross-mark DEMAND witnesses |
|---|---|
| run-1 | `F_T`, `F_U` |
| run-2 and every even run through run-30 | `B_T`, `B_U` |
| run-3 and every odd run through run-31 | `F_T`, `F_U`, `Ff` |

The fine NE/NORMAL rows in the proposal trace are covered by the proof's
extra-state closure, not attributed to this old native trace. Formal proof
uses constructive Lean only; no custom axioms, holes or external proof oracle.
Source hashes are checked for all reused proof dependencies. Bulk logs and
compiled artifacts remain outside the repository.

No production semantic change or new repair is selected by this investigation.
The ordinary diagonal read/write candidate rejected during this search is
not evidence: its diagnostic model had omitted existing DEMAND-FLOW coverage.

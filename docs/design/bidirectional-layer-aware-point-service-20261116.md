# Separate NORMAL closure from plain return service

Later investigation found an
[historical relevant-protected-return case](../reports/bidirectional-relevant-protected-return-nontermination-20261117.md).
The two-rule one-mark reference repeats complete **run-9/run-10** states
uncapped. NORMAL-layer closure succeeds; relevant protected returns and
protected current replies retain the explicit vetoes specified below.
The unrelated-return repair and its older example results remain valid.
The later [same-flag repair](bidirectional-flag-aware-reply-service-20261117.md) now closes that case at run-5; stored flags remain separate.

16 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
[Consolidated approach](bidirectional-demand-termination-approach-20261115.md).

The [protected unrelated-return example](../reports/bidirectional-protected-return-nontermination-20261116.md)
now stops naturally at **run-5**, with its NORMAL observation retained.
It previously repeated complete run-11/run-12 states without a limit.
The older h-read, exact-input and V-return cases retain identical semantic
cold histories. Their natural stops remain run-5. The largest retained
older reference stops at run-15. Latest unchanged native diagnostic:
**run-31/POLICY**.

## 1. Selected change

This is a **major completion-eligibility and current-DEMAND-return delivery
change**. It is not a change to the propagation layer or protection rules.

| Part | Before | After |
|---|---|---|
| Full NORMAL closure | Every processed state must be NORMAL and plain | Every processed state must be NORMAL; retain its literal H |
| Reply-specific terminal service | Plainness was required for every raw return | Require plain service for every overlapping return |
| Protected return outside the reply region | Blocks all completion | Does not block this reply's terminal service check |
| Protected return overlapping the reply | Blocks selection | Still blocks selection, even with protected NORMAL service |
| Protected fact or current protected reply | Existing handling | Unchanged; never erase H or select that reply for removal |
| Whole/mark fast paths, C2/C5, transfers, marks, caps, receipts, persistence, Targets | Existing handling | Unchanged |

The change moves the plainness requirement from the full body to the relevant
terminal obligations. NORMAL remains a layer. H remains an independent literal
membership. No cross-H subsumption is introduced.

## 2. Two explicit predicates

For each scalar fact membership c:

```text
normalLayer(c)  := c.layer == NORMAL
plainService(c) := normalLayer(c) and c.H == 0
```

Use `normalLayer` for the existing full-closure eligibility check. Use
`plainService` for the return service that can justify omitting a plain
current DEMAND reply.

Do not rename a protected NORMAL fact to DEMAND. Do not clear H, merge plain
and protected memberships, or let a protected provider cover a plain return.
Source assignment, cleaner-survivor and cycle-protection rules stay unchanged.
Pass rules still carry H and never create it.

The old whole/mark certificate implementations keep their stricter checks as
conservative fast paths. They need not grant a flag in the new case. The
current-owner reply-specific path supplies the new opportunity.

## 3. Closure and service

Use the existing query eligibility: restricted forward FULL, run >= 3,
already owned concrete EXACT initial I with NORMAL actual support, Empty E/mx
and plain original H. Do not add an initial or broaden C2 admission.

```text
C = existing processed states of I, with their complete H memberships
R = full, uncut, mode-stable native transfer relation

ClosedNORMAL(I,C) :=
    seed(I) in C
    and forall s in C: s.layer == NORMAL and R(s) subset C

Relevant(c,reply) := possibleRegion(c) overlaps possibleRegion(reply)

CompletePlainReply(I,reply) :=
    ClosedNORMAL(I,C)
    and forall real return c in C:
        if Relevant(c,reply):
            c.H == 0
            and an admitted plain NORMAL row covers the WHOLE c
            and that row's whole NORMAL image actually applied here
```

**Do not remove H=1 states from C.** Process every strong transfer from those
states. An internal protected state can lead to a relevant return. The full
closure must include that return too. Projection applies only to terminal
service obligations.

**Do not remove H=1 returns from Relevant.** If one overlaps the reply, veto
this additional selection. This conservative rule preserves the selected
separation of literal H classes. It does not claim that every such case can
be optimized.

Any DEMAND state, real cut, unfinished operation, unclosed dependency,
unsupported effect or missing state still prevents full NORMAL closure,
even outside the reply's region. Do not raise a field limit or rerun precise
analysis to obtain closure. A partial child reply certificate is not a full
child transfer relation. Keep the existing conservative adapter boundary
for ND, negative conditions, cleaners, statics, aliases and opaque effects.
The executable leaf adapter still uses the same ordinary allocation/return
and positive unary marking transfers.

The overlap test, owner-side bound reply geometry, whole-native-cover test,
original binding, physical ports, revision and continuation checks stay as
specified in the reply-scoped proposal. H is not a reason to call two
geometrically overlapping returns disjoint.

## 4. Single delivery algorithm

```text
onCurrentReturnReply(context, actual, currentRow, boundReply, normalPacket):
    // Saved NORMAL replay and current NORMAL application already ran.
    if the existing whole/mark certificate and receipt suffice:
        use the existing selection
        return
    if not oldPlainCurrentReplyGuards(context, actual, currentRow, boundReply):
        deliver(boundReply)
        return
    if not owner.hasCurrentClosedNORMALBody(actual.rawExactKey, context):
        deliver(boundReply)
        return

    region = ownerSideRegion(boundReply)
    for c in owner.existingProcessedReturns(actual.rawExactKey):
        if possibleOverlap(c, region):
            if c.H != 0:                    // relevant protection is a veto
                deliver(boundReply)
                return
            n = admittedWholePlainNORMALCover(c, actual.rawExactKey, context)
            if n is absent or its whole NORMAL image did not apply here:
                deliver(boundReply)
                return
    omit only this plain current DEMAND DATA membership
```

The old guard still requires a NORMAL concrete EXACT actual, plain original,
Empty E/mx, a strict shorter-prefix STAR premise and a plain CURRENT DEMAND
concrete return. NORMAL/protected replies, FLOW, non-return effects,
ZERO/Targets, requests and subscriptions remain outside this selection.
Saved NORMAL replay stays first and unchanged. No caller waits for a new
barrier; an already emitted Target remains emitted.

For a packed fact, use scalar memberships or equivalent existing masks.
The packet's propagation layer may be NORMAL while some memberships have H=1.
Do not reject the whole packet merely because its protection mask is nonempty.
Select all overlapping memberships, then veto if any selected one is protected.
Compare provider and selected plain membership with the existing exact
protection coordinate. Retain both plain and protected copies at an identical
AP/mark coordinate. Do not OR-collapse them.

## 5. New example

The analyzed code and its protection are unchanged:

```java
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x=make(a).h;
    Box y=make(x).h;
    Box z=make(y).h;
    // Observe CM(z.M,U).
}
Box make(Box p) {
    Box r=new Box();
    // For (m,n) = (T,U), (U,T):
    // CM(p.f.g.g.M,m) => assign n to r.h.MUST.
    // CM(p.M,m) => assign n to r.h.h.MUST.
    // CM(p.M,m) => assign m to r.k.MUST.  // same-mark assignment: H=1
    return r;
}
```

At the first precise call:

```text
actual and initial: p.f.g.$/T,N,H=0
full raw returns:
    ret.h.h.MUST/U,N,H=0
    ret.k.MUST/T,N,H=1

reply region: ret.h.M/U
admitted and applied plain NORMAL service: ret.h.h.MUST/U
```

Before, `raw.all(!DEMAND && !H)` refused the body because of k.
Now, both returns have the NORMAL layer. The full body can close with k
still protected. k is disjoint from h/U. Every overlapping return has plain
NORMAL service, so the coarse h.M/U delivery is omitted. The caller keeps
x.h.MUST/U,N,H=0. No protected fact is changed or used as a plain provider.

| Run | Before: helper demand rows | Updated rows | NORMAL records | Whole / mark / current closure keys | Root state |
|---|---:|---:|---:|---:|---|
| run-1 | 6 | 6 | 0 | 0 / 0 / 0 | DemandTarget |
| run-2 | 6 | 6 | 0 | 0 / 0 / 0 | entry-marking permission |
| run-3 | 15 | 4 | 1 | 0 / 0 / 1 | earlier DemandTarget retained |
| run-4 | 40 | 11 | 1 | 0 / 0 / 0 | entry-marking permission |
| run-5 | 42 | 0 | 10 | 0 / 0 / 3 | NORMAL observation; natural stop |

The protected k NORMAL return is still not archived as a summary when C5
rejects it. The owner uses the existing processed body states for closure.
[Complete updated per-block trace](../reports/bidirectional-layer-aware-point-service-trace-20261116.md).

Controls show the retained boundary:

```text
k/U,N,H=1 outside h/U:             may close h, if all other checks pass
h.h/U,N,H=1 overlapping h/U:       keep the plain DEMAND reply
h.h/U,N,H=0 with only H=1 provider: keep the plain DEMAND reply
k/T,D,H=1 outside h/U:             full NORMAL closure fails
```

## 6. Storage, work and field limits

Reuse the existing query coordinator's current-epoch closure status. Its
meaning is now NORMAL-layer closure with H preserved. It is not a new fact
label or GroundingSupport. Fact equality, hashing, MethodEdgeStore and both
H columns remain unchanged. No new query, summary, field path, region table,
negative cache or caller history is added.

This change makes an existing closure test less restrictive. It does not
launch extra transfer or bind more rules to prove completion. When existing
processed states or complete native-transfer support are unavailable, keep
ordinary delivery. Do not create an unrestricted summary archive or reconstruct
field suffix evidence across calls.

The same local bounds remain: one current status per already owned query;
one scan of its existing body state for closure; at most B*R overlap/service
checks for B eligible reply leaves and R owned return leaves, with existing
path and native-cover lookup costs. H is checked only as a terminal veto after
region selection. Whole/mark fast paths and within-packet reuse remain.
Decisions do not persist per region. For a fixed plan and packet this is a
selection of existing replies. No global whole-run speed or membership-subset
theorem is claimed: later demand frontiers can change.

```text
ordinary initial: FL(I) <= min(globalLimit, FL(own Dc)+1)
summary output:   FL(C) <= min(globalLimit, FL(own Dp)+1)
real cut:        NE/DEMAND, preserving the existing mark and H behavior
```

No exception is added. The only retained entry-cap exception remains the
previously enumerated NORMAL-MUST actual with a deeper real hole. This new
selection uses EXACT actuals and cannot activate that exception. The new
example uses none; every output cap remains mandatory.

## 7. Proofs and old examples

[Constructive proof package](../../spec/lean/proposals/layer-aware-point-service-20261116/README.md):

1. NORMAL layer and plain service are distinct predicates. Relevant protected
   returns always veto the new check. Native receipt equality retains H.
   A protected provider cannot cover plain service; both memberships remain distinct.
2. The full internal closure still contains every protected state and successor.
   Every relevant reachable plain return has a whole admitted NORMAL witness
   and an actual same-context native image. The existing generic continuation
   observation theorem applies with the stricter plain terminal service.
3. Every old certificate remains valid. When all old raw returns are plain,
   the old and new reply predicates are equal. The whole/mark fast paths are
   source-identical; their stricter eligibility is retained.
4. Complete cold transitions and within-run fixed points prove the new run-5
   stop, retained NORMAL observation, and an inductive uncapped quiet suffix
   from run-6. The run-3 Target is not canceled.
5. The old h-read, exact-input and V-return cases are rerun with this coordinator.
   Complete semantic cold states through run-6 equal their earlier states after
   only namespace/representation translation. Each still stops at run-5.
6. The old-guard bridge retains all older guard-ineligible ordinary references,
   including the real-hole/alternating checks. FLOW/MUST/DEMAND actuals and
   protected current replies retain their old guards. The largest retained
   reference stops at run-15. No new adapter for older unsupported effects is inferred.
7. Query-key membership, selection-subset, C2/C5 cap and Target-accumulation
   proofs remain valid. There is no protected k summary archive and no falsely
   granted whole/mark flag in the new case.

These are scoped results for the stated adapter and supplied examples.
A relevant protected return deliberately remains a veto; incomplete/DEMAND
closure and unsupported native effects still fall back. No universal termination,
whole-engine/JVM/alias equivalence or project-performance theorem is claimed.
At this repair's original validation point no unresolved supplied ordinary-code
example was known. The later relevant-protected-return case linked above now has the same-flag repair.

## 8. Validation

The proof audit passes **177 new constructive claims; 6,279 cumulative claims
in 324 source-hash-checked modules**. Only `propext` and `Quot.sound` occur
in new proof dependencies; no classical choice or custom axiom is used.

All **57 native component/control tests pass**, including eight new tests.
They check disjoint protected NORMAL returns, same-mark disjoint protection,
relevant protected veto, wrong-H providers, NORMAL/protected/FLOW retention,
unfinished/DEMAND work, receipts, scope, direction and mode.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/layer-aware-point-service-20261116/check.py \
  --out /tmp/layer-aware-proofs

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.LayerAwarePointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ProtectedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.ReplyScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.UnadmittedFieldCycleTest \
  --tests org.opentaint.dataflow.bidi.ScopedPointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.UnadmittedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.CompletePointServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest \
  --tests org.opentaint.dataflow.bidi.ExcludedHeadAdmissionTest --offline
```

The unchanged full-program native diagnostic reaches run-31/POLICY with zero
NORMAL reports; the proposal reference retains its NORMAL observation at
run-5. These component tests do not install the complete NE/completion proposal
or establish full-engine equivalence. Production is unchanged.
Full captures, test XML, compiled proofs and audit receipts remain outside the
repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/layer-aware-point-service-20261116/`.

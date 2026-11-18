# Complete native-bound NORMAL reply service

17 November 2026. Synthetic data-flow reachability. FULL acceptance mode.
Follow [proof-guide.md](../../spec/proof-guide.md). Production stays unchanged.
This extends the [consolidated approach](bidirectional-demand-termination-approach-20261115.md).

## 1. Selected change

The previous same-H rule requires a plain caller input and a shorter STAR
premise. These guards can retain a coarse DEMAND return after its actual
NORMAL answer is complete. A protected caller input exposes this case.
An exact-premise summary with a cut conclusion exposes a second case.

Use **complete native-bound NORMAL service** to select current DEMAND DATA
replies. Compare actual applied images, including protection transport and
mark restoration. Do not compare stored H with caller H. Keep the two stored
H memberships separate.

These are major semantic changes to current reply delivery:

| Part | Before | New |
|---|---|---|
| Caller protection | The new service path rejects H=1 inputs | It can use their own complete, already applied NORMAL answers |
| Current DEMAND premise | Only a shorter STAR premise can use service selection | Any applicable unary non-ZERO premise can use it; the reply must be concrete return DATA |
| Strong actual query | The closure adapter accepts NORMAL EXACT | It also accepts an already owned NORMAL MUST query; retain its actual E |
| Terminal service | Require a literal raw return image | Also accept whole NORMAL MUST coverage after actual-data canonicalization |

The old whole-query, mark, plain-region and same-H fast paths remain valid
with their existing guards. The new path is additional. It does not change
summary storage subsumption or remove owner DEMAND records.

## 2. Eligibility and ownership

Use the exact current owner, revision, physical ports, original premise,
actual packet, full mark and application context. The actual must be NORMAL
and concrete. It must be EXACT with empty E, or definite MUST with its real E.
Mark exclusions must be empty. A query for that actual must already exist. A strong query here is an
ordinary C2-owned NORMAL EXACT/MUST query. This adds no StrongQueries
entrypoint or permission.
A historical closure key alone is not evidence.

Require complete current NORMAL closure of the whole owned query graph.
Do not project internal states by mark, H or output region. Every transfer,
call effect and boundary effect in the supported adapter must be accounted
for. Any missing transfer, pending effect, cut state or unresolved DEMAND
state prevents closure. An adapter that cannot establish completeness falls
back to ordinary delivery. Add no query to obtain a certificate.

The concrete executable adapter in this package covers positive unary
marking actions on a fresh returned object, ordinary allocation/return,
and the caller's ordinary field reads. Its raw result list is finite and
comes from those actions. It is not a general-purpose raw-summary archive.
The generic graph theorem applies only after full closure is established.
It does not assert that every production method has such an adapter.

## 3. Selection algorithm

`bind` means the existing native summary application in the actual context.
It includes incoming H, stored conclusion H and any existing mark-cycle
protection. Use its real result; do not rebuild a transfer with a different
matching policy. The leaf model's `readBound` corrects its old omission of
incoming-H transport. Native tests show that production already transports
this H. This is a model correction, not a production transfer change.

```text
replies(actual, original, owner):
    saved = applySavedNORMALRecordsFirst(actual, original)
    current = owner.currentRecordsApplicableTo(actual)
    applied = applyNormally(current, actual, original)
    native = committedNORMALImages(saved + applied)

    for (record, result) in applied:
        if result is NORMAL or is not concrete return DATA:
            deliver(result)
            continue

        q = owner.existingNORMALExactOrMUSTQuery(actual)
        if actual is not NORMAL EXACT/MUST or q is not fully NORMAL-closed:
            deliver(result)
            continue

        obligations = all terminal returns of q that overlap result.region
        obligations = obligations whose native bound H equals result.H

        if every c in obligations has n in native such that:
              n belongs to this same application context
          and n is NORMAL
          and n.mark == bind(c).mark
          and n.H == bind(c).H
          and n wholly covers bind(c):
            omit this current DEMAND DATA delivery
        else:
            deliver(result)

    // Keep owner records, handoff demand, persisted records and prior Targets.
```

A real implementation can borrow the applied NORMAL packet and its existing
record handles. It must not apply summaries twice. The executable reference
enumerates the finite supported return set to check its certificate.

Same H means the H of the **bound image**, not the H of the stored owner row.
A plain owner row can bind to H=1 because the incoming packet has H=1.
A local mark cycle can also protect the bound output. This does not merge
stored protected/plain rows. A pass does not create protection; it only
carries the existing flag.

Whole coverage is equality, or the retained NORMAL MUST actual-data cover
with the same base, full mark and bound H. Respect field exclusions. Partial
overlap is not coverage. A NORMAL uniform value outside a real hole can
cover a child image removed by canonicalization. It cannot cover the hole.

Saved replay stays unchanged and runs first. This proposal does not select
saved provisional effects. Current owner DEMAND records remain in handoff,
including records useful for different future actuals. Apply the test before
allowing a new current DEMAND continuation to create a coarse caller result.
Never retract an already emitted Target.

## 4. Why no required route is lost in the proved scope

Let Q be the complete owned graph for a strong actual. Closure includes all
seeds and every successor of each owned state. Induction on reachability
puts every possible return in Q. For a selected return c, the certificate
constructs a committed NORMAL witness n in this exact caller packet.

```text
reachable(c) AND selected(c)
    => exists n in committedNORMAL : wholeCover(n, bind(c))
    => every covered concrete observation from bind(c) remains available
```

The proof handles arbitrary continuations whose concrete observations respect
whole coverage. A finite set of observations has simultaneous witnesses in
the same packet; witnesses cannot be borrowed from incompatible callers.
A missing relevant return, wrong H, missing NORMAL image, unknown child effect,
or incomplete owner closure rejects selection.

This is context-local delivery selection. It does not erase the conditional
owner record. Its reverse demand remains available at handoff. Previously
persisted NORMAL records also remain and replay first. For the two new
programs, complete cold transition proofs establish the later permissions,
NORMAL observations, within-run fixed points and an uncapped quiet suffix.
This is not a whole-engine termination or model-equivalence theorem.

## 5. Bounds and costs

No new global, FL(Dc)+1 entry or FL(Dp)+1 output exception is introduced.
The existing enumerated MUST/real-E head policy remains as specified; this
change adds no case to it. Query preparation and C5 are source-identical.
A cut or incomplete query cannot supply full closure.

Let B be current candidate replies and R be existing applied NORMAL images
plus owned terminal obligations. A borrowed linear implementation uses at
most O(B*R) checks and O(R) temporary references. It can share the bound view
within the existing packet. It creates zero additional queries, field paths,
summaries or subscriptions. Keep no permanent per-region table, caller
history, unrestricted suffix evidence or raw-candidate archive. The selected
current delivery is a subset of the old one.

Closure detection must use the existing bounded query execution. Do not run
an unbounded field-sensitive analysis to obtain the full return answer.
Unsupported adapters use ordinary delivery. The new certificate removes
avoidable coarse continuations; it does not guarantee a speedup where
strong NORMAL closure is unavailable.

## 6. Examples and validation

Protected-input program:

```java
// Entry marking: T at a.f.g.$ only.
void root(Box a) {
    Box x = make(a).h;
    Box y = make(x).h;
    Box z = make(y).h;
    // Observe CM(z.M,T).
}
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T at r.h.MUST.
    // CM(p.M,T)       => assign T at r.h.f.g.$.
    return r;
}
```

The first call gives NORMAL protected x.f.g.$/T. The next actual is therefore
protected. The old plain-original guard rejects its complete NORMAL answer.
The new check uses that answer's bound H=1 image. It also handles the exact
premise whose result was cut by C5.

| Reference | Previous result | New result | NORMAL observation |
|---|---|---|---|
| Protected caller input | Proved uncapped run-9/run-10 cycle; 39/45 helper DATA rows | Natural stop run-7; one retained NORMAL record | Retained from run-5 |
| Uniform-input, alternating-mark control | Finite run-9/run-11 repetition; not an uncapped counterexample claim | Natural stop run-9; eight retained NORMAL records | Retained from run-7 |
| Five earlier service programs | Natural stop run-5 | Natural stop run-5 | All retained |

The uniform control starts with T at a.f.g.MUST. Its deep guard is p.f.h.g.M.
Both actions assign the other mark at r.h.MUST and r.h.f.g.MUST. Three calls
observe U. It uses only ordinary code and positive marking/observation rules.

[Complete annotated traces](../reports/bidirectional-native-bound-reply-service-trace-20261117.md)
show every cold run. [Proof package](../../spec/lean/proposals/native-bound-reply-service-20261117/README.md)
lists the claims and reproduction commands. Earlier ordinary, protected and
cleaner results keep their separately stated proof scopes; unsupported
adapters use fallback. No older example is removed from the acceptance set.

The unchanged production diagnostic still reaches run-31/POLICY and has the
previously documented NORMAL-observation difference from the scalar reference.
The new native checks validate component contracts, not integration of the
whole proposal. No project performance result is claimed.

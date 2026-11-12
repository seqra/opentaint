# Retire a closed FLOW frontier with NORMAL replay

11 November 2026. This is a candidate campaign predicate, not a production
change. Reference: `14d7b63369d94f49d4c551be8405ed7719f267cc`.
Original reached / completed / accepted forward runs: OWASP 11/11/11,
Conductor 8/7/7, Stirling-PDF 11/10/9.

## 1. Selected change

The candidate removes repeated FLOW demand after the later completed run.
It extends [source-safe replay](source-safe-normal-replay-demand-retirement.md)
to a closed owner whose current nonstatic frontier contains FLOW only.
Unlike that predicate, it can remove a C2 entry with no duplicate entry.

Keep all retained NORMAL records, legal saved NormalTargets, source
permissions, rule contributors, reports and unrelated demand. Keep initial
emission, C5, field limits, transfer, matching roles, layers and protection.
Do not add a companion analysis, special tail, source event or new NORMAL
record. Do not change the production analyzer.

The contract is [P's required concrete-path contract](normal-backed-flow-demand-retirement.md).
It permits removal of speculative MAY combinations. It does not assert equal
arbitrary AP packets, callback order or work counts.

This is stronger than an edge-shape test. All guards below are necessary for
this candidate. A failed or unknown guard leaves the target OPEN.

## 2. Closed owner state

Use one exact method/context with no loop. Let its nonstatic interface lane
be A to B forward and B to A backward. For the first case, A is `this` and B
is `ret`. Require these checks at the completed barrier:

1. Every actual projected owner row is unary nonstatic FLOW DATA in that
   paired lane. There is no concrete, ND, ZERO or Target control entry.
2. Every resolved child scope has empty local demand. The finite call closure
   is complete and acyclic. No unknown callee or predefined effect is hidden.
3. All saved AP providers in every scope are FLOW-to-FLOW copies, isolated
   static same-mark identities, or ZERO identities. In particular, no saved
   FLOW/ZERO-to-concrete DATA generator exists.
4. The source forms contain ordinary copies, selected cleaners and positive
   unary concrete source/sink conditions only. Boundary GEN, ND, static
   mutation and stage triggers are empty. Static and nonstatic lanes do not
   cross. Keep all actual aliases in the copy bound.
5. The run is restricted FULL, run-3 or later. Native validation forbids
   shared static carry and static completion at these runs. Actor creation
   adds no ZERO. Requests and static operation resumes are run-1 mechanisms.

Saved NormalTargets need not be absent. Every legally published Target has
concrete or ZERO premises: native `emitTarget` checks that no premise member
is FLOW. A raw FLOW fact cannot satisfy those concrete or ZERO premises.
Do not treat this check as a silent filter; the invariant must prevent an
invalid callback. Saved replay at an outer call remains before C2. A lost
inner call has no matching saved Target from its FLOW input.

## 3. Frontier induction

A FLOW demand renders FLOW initials, even when its actual offer has concrete
T. All emitted companions are also FLOW. A concrete entry cannot admit a
FLOW actual; its companion needs a successful concrete primary. The selected
owner has no such concrete entry or ZERO control entry.

Copies, binding, selected FLOW cleaning, field cuts and FLOW summary
application keep the FLOW mark lane. Concrete positive guards do not hold.
Saved contributor restoration requires a current `MarkCheck.Holds`; a FLOW
input cannot restore a marked contributor. Thus no lost FLOW job creates a
source hit, marked rule output, sink seed or Target.

At a child call, saved NORMAL replay runs first. Its typed providers preserve
the lane. Empty child demand admits no current child initial or subscription.
No child publication is added, so the child's next demand stays empty. This
is a checked conditional runtime fact. It does not declare NORMAL records
to be the unconditional semantics of the child method.

C5 keeps the admitted original and matches the output base to one complete
paired exit. It changes neither endpoint base nor the FLOW lane. Handoff
reverses the paired lane. Therefore the owner frontier remains FLOW-only in
the same two bases after each later local transition. Child frontiers stay
empty. New persisted owner copies remain FLOW copies in that selected lane.

This induction is required. A single observed FLOW job is insufficient when
another admitted job could publish a concrete result to the same caller.

## 4. Complete boundary replacement

Omitting a FLOW start can omit a real subscription whose raw caller fact has
T. Type purity alone does not prove that subscription redundant. It can carry
a current FLOW summary back to a concrete caller.

For each direction, build a complete conservative paired copy relation from
the actual directional CFG and CallPoint plans. Use native saved child replay
only after proving that child C2 is empty. Keep all source/body evidence too.
Restrict the relation to the owner's possible admitted input base and paired
C5 output base. Preserve input/output suffix correlation and masks.

Every required selected boundary row R must have an independently retained
NORMAL replay witness N under P's native coverage rule:

- Full owner, context, interface and endpoint bases match.
- One suffix extends both N endpoints to R.
- N excludes no mark that R can transfer.
- Same-direction N accepts the complete lost input region. A reverse record
  retains its actual `SAVED_OPPOSITE` read role.
- The witness is a persisted admitted NORMAL, not a raw or proposed record.

Only then can each current copy delivery lost with a subscription use N on
the original caller offer, before C2. Preserve required point mark, layer,
protection, aliases, return actions and field cuts under P's existing bridge.
The proof must cover all selected outputs of the lost starts, not just X's
displayed output path. Other public outputs can be ignored only when every
possible paired exit in the proved frontier rejects their base.

## 5. Executable candidate

```text
closedFlowReplay(removals, completedState):
    closure = exactClosedOwnerAndChildKeys(removals)
    require lateRestrictedFullPolicy(completedState)
    require completeOwnerFlowOnlyLane(completedState, closure.owner)
    require allChildDemandEmpty(completedState, closure.children)
    require sourceAndSavedProviderTypeSeparation(closure, completedState)
    require legalSavedTargetPremises(closure)

    for direction in [FORWARD, BACKWARD]:
        copies = completeDirectionalBoundaryBound(closure, completedState)
        selected = restrictToProvedLane(copies, direction)
        for R in selected:
            require nativeNormalReplayWitness(R, direction, completedState)

    require constructiveFrontierAndDeliveryProofIsBoundToTheseGuards()
    require priorDependenciesRemainValidOrHaveExplicitReplacementProofs()
    return perTargetCertificates(removals)
```

The proof check in this pseudocode means the named, checked constructive
model and its full source/native binding. It is not an input Boolean or an
assumption that later behavior is equivalent. The implementation must expose
the finite guards and witness data used by that proof.

## 6. First case and present limits

The current target is Conductor `33399e0e…`:

```text
this.*/FLOW -> ret.[any]/FLOW, DEMAND
pair: run-5/run-7; proposed removal: after run-7
next run: run-8, BACKWARD
```

The original owner has seven FLOW rows. Four have accepted source-safe replay
certificates, leaving three. Both child frontiers are empty. The complete
saved basis has 67 directional memberships: 55 FLOW copies, nine static
concrete identities and three ZERO identities.

Actual backward plans give these four selected boundary rows, for arbitrary
common suffix s and e = `java.util.Optional.Element`:

```text
ret.s   -> this.s
ret.s   -> this.e.s
ret.e.s -> this.s
ret.e.s -> this.e.s
```

All have retained native NORMAL witnesses. Two extra Return-to-Return rows
in the wider stage-pass bound fail every paired This exit. Replacing child
body expansion with actual saved replay plus empty C2 gives the same four
selected backward rows. The forward selected lane has its own checked bound;
do not infer it by reversing the backward table.

This evidence does not yet accept a predicate. The constructive frontier and
delivery proof, new native bridge, independent review and complete global
filter remain acceptance gates. The retained `21aded9d…` entry witness is a
dependency of four accepted certificates. It cannot retire unless each old
proof is explicitly replaced. Preserve the old proof packages unchanged.

The candidate does not cover mixed marked frontiers, ZERO admission, loops,
unknown callees, nonempty child demand, mark-changing saved producers or
arbitrary rule generators. No failed guard proves necessity.

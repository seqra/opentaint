# ZERO-premise loop output bypass: selected rule

8 November 2026. Selected for the updated specification. Reference baseline
`52829d5890ec3b3145cc996a1d8162d85cb8ceda`. No production change.
Latest analyzed phase: **run-5**, forward, field limit 4.

The filename and original Candidate Lean namespace are retained for evidence
links. The normative rule is now in section 6.3 of the
[combined spec](edge-subsumption-initial-emission-demand-intersection.md).

## Rule and scope

An applied loop summary with its own effective ZERO premise bypasses the
extra loop output restriction. A DATA-premise summary keeps the existing
restriction: apply it only when the stored conclusion is deeper than the
stored premise. Keep the existing ND arm test.

This changes which loop results are retained. It applies to NORMAL and
DEMAND ZERO-owned results, in both directions. A DEMAND result stays
DEMAND. This does not exempt a summary from C5 intersection before
publication, the global field limit, liveness or output deduplication.
It does not add ZERO admission, a source permission, a FLOW companion,
an ANY premise, a Target conversion or completion guidance.

```text
// Publication is unchanged:
// normalize the candidate, apply paired C5, store and publish admitted rows.

onAppliedLoopSummary(row, parentOriginal, appliedValue):
    F = applyGlobalFieldLimit(appliedValue)
    if row.effectivePremise == ZERO:
        results = [F]
    else if existingStoredShapeTestSaysGrowing(row):
        results = restrictLoopOutput(F)
    else:
        results = [F]
    for result in results:
        deliverFreshAtExistingBoundary(parentOriginal, result)
```

Use the row's premise, not `parentOriginal`. After a source, the parent
original can remain ZERO while the applied row is a growing DATA
transform. That DATA row must still pass the loop restriction.

For an opposite-direction saved record, use the effective premise after
reversal. Do not use the stored record's old premise. A genuine ND premise
is DATA and gets no ZERO exemption, even when its matched parent origins
combine to ZERO. Typed Target outputs keep their existing terminal path.

## Why this is a useful distinction

A canonical ZERO input has no field suffix. Replaying one fixed
`ZERO -> C` summary gives the same geometry C, with the existing joined
support. It does not append a caller suffix on each repeat. Existing
boundary storage deduplicates that repeated result.

A DATA summary can copy the incoming suffix and add a field prefix.
For example, repeated `x.* -> x.f.*` application grows the path. This is
the feedback which the loop output restriction still controls.

The global limit still bounds every delivered field chain. With a finite
fact alphabet, the per-run shape space remains finite. This is not a claim
that the space is small, or a proof of convergence across analysis runs.
New ZERO summaries can still cause more finite work than the old heuristic
allowed. Measure that effect when this rule is implemented.

## The diagnosed run-5 case

The [root-cause trace](subsumption-loop-saved-replay-root-cause-20261108.md)
already derives the following source row through C5:

```text
Local ZERO -> x.f.f.f.$/T, NORMAL
    ZERO bypass: deliver x.f.f.f.$/T,N to the repeat input
    saved x.f.*/FLOW -> x.*/FLOW,N: x.f.f.$/T,N
    same saved summary:             x.f.$/T,N
    existing exact demand:          initial x.f.$/T,N
    ordinary read and sink:         x.f.$/T -> NormalTarget(id),N
    ordinary parent application:    ZERO -> NormalTarget(id),N
```

The saved reads have shrinking stored geometry. They already bypass the
extra gate. Thus only the first source delivery needs this new rule.
No `x.f.[any]` completion is needed for this route.

## Evidence and implementation seam

The [Lean candidate](lean/proposals/subsumption-initial-demand-20261107/ZeroPremiseLoopBypassCandidate.lean)
checks the unchanged reached run-2 and run-3 fixed points in the declared
repeat component, the run-5 source delivery and existing sink route,
unchanged DATA-row behavior, retained global cuts, retained DEMAND support
and the distinction between local premise and parent original.

The native component test uses a test-only policy adapter against the
frozen baseline. It changes no production code. It checks the positive
ZERO route, the negative DATA-grower case under parent ZERO, and a global
cut before the bypass. The original gate/source/read/sink/Target checks
remain in the same test class. This is not a full redesigned driver run.

All eight native component tests pass. The
[test source](lean/proposals/subsumption-initial-demand-20261107/native-zero-loop-bypass-candidate-20261108/LoopSavedRepeatGateDiagnosisTest.kt)
and [receipt](lean/proposals/subsumption-initial-demand-20261107/native-zero-loop-bypass-candidate-20261108/receipt.json)
are in the repository. The
[Lean receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1132.json)
and [axiom audit](lean/proposals/subsumption-initial-demand-20261107/component-axioms-1132.txt)
include the 11 new local candidate statements. No complete native-driver
or general loop-convergence result is claimed.

When implemented, change both runtime paths. `onData` has the current or
same-direction saved row's premise. `applySavedView` has the effective
reversed premise. Both must pass the correct restriction decision to
`onApplied`. That method calls the Boolean overload of the gate. Changing
only the gate's `PremiseKey` overload would change a unit test without
changing these runtime decisions.

This selected rule fixes the diagnosed ZERO/source loss. It does not prove
that every DATA-premise loop restriction is safe. A growing DATA producer
can also have a useful saved-repeat continuation. That separate general
obligation is unchanged; the bypass must not be broadened to parent ZERO
to claim that it closes it.

Finalization status: no complete additional FN-producing DATA-premise
program is currently established under the finalized FULL rules. The
general continuation argument above remains a proof/implementation check,
not a claim of another demonstrated program loss.

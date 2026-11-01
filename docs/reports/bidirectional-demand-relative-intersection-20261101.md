# Evaluation of a demand-relative conclusion limit at C5

Date: 1 November 2026. Runtime:
`c4a71246519ee5432879ce82518823f1703f3aa4`.
This is an analysis of a candidate policy, not an implementation spec.

User clarification: all new summary edges must be restricted with demand,
including NORMAL edges. There is no unrestricted NORMAL-summary exemption.
The earlier recommendation to preserve raw NORMAL persistence as part of
this candidate is withdrawn. Raw persistence below describes the current
implementation. The intended admitted summary set is the result of
restriction and the selected collapse. Existing record persistence and
next-run demand extraction must use that admitted set.

The closed campaign reached Stirling-PDF **run-8** (run-7 complete and
accepted) and conductor **run-4** (run-3 complete and accepted). These are
FULL, 16 GiB results with limits `1,1,2,3,…`. No new project experiment is
included here.

## 1. Meaning of the two bounds

Let an edge from the preceding run be `Dp -> Dc`. Its demand pair for the
current opposite run has:

```text
entry = Dc       // selects the current initial A
exit  = Dp       // selects the current conclusion B
```

`FL` counts concrete AP fields and array elements. It does not count a
static class accessor or a wildcard tail.

The proposed conditions are:

```text
FL(A) <= FL(Dc) + 1

For each matched pair:
  selected = existingC5(A -> B, Dc, Dp)
  published = currentFieldCut(selected, min(runLimit, FL(Dp) + 1))
```

The initial bound already follows from the current scalar C2 policy.
`RestrictedInitialPolicy.emit` retains the demanded prefix or stops after
the first new counted field. Summary normalization from abstract EXACT to
STAR does not change field depth. The bound applies to each admitted
singleton initial. A full ND original needs the corresponding bound for
each contributing member and its complete matched support.

The second bound is new. It uses the previous demand's output selector,
not the current original premise. Those are different quantities.

## 2. Current C5 permits deeper conclusions

`Reference.restrictConclusionOnly` explicitly keeps a descendant unchanged:

```kotlin
q.startsWith(p) -> if (dp.tailAdmits(q.drop(p.size))) sc else null
```

Here `p` is `Dp.path`, `q` is the raw conclusion path, and `sc` includes
the raw layer. No `FL(Dp)+1` test follows this branch.

A legal current query is:

```text
Previous demand: p.[any]/T -> ret.[any]/T
Current A:      ret.f.$/T                 FL(A)=1, FL(Dc)=0
Raw B:          p.a.b.c.$/T               FL(B)=3

Current C5:     ret.f.$/T -> p.a.b.c.$/T   retained unchanged
Proposed cut:   ret.f.$/T -> p.a.[any]/T   DEMAND
```

The current conclusion exceeds `FL(Dp)+1 = 1`. This is an accepted
production C5 shape, not a claim that these field names were captured in
Stirling or conductor.

Three external controls exercise current C5 and a caller-side application
of the proposed post-selection cut. All three pass. For the same depth-3
raw NORMAL conclusion:

| `Dp` | Current C5 output | Output after proposed cap |
|---|---|---|
| `p.[any]/T` | `p.a.b.c.$/T`, NORMAL | `p.a.[any]/T`, DEMAND |
| `p.a.[any]/T` | `p.a.b.c.$/T`, NORMAL | `p.a.b.[any]/T`, DEMAND |
| `p.a.b.[any]/T` | `p.a.b.c.$/T`, NORMAL | Same precise NORMAL output |
| `p.a.b.c.[any]/T` | `p.a.b.c.$/T`, NORMAL | Same precise NORMAL output |

EXACT selectors at the shallower prefixes already reject the deeper
conclusion. The controls also retain the protection annotation. Their raw
NORMAL persistence check describes the current implementation; it does
not establish the clarified policy for persistence of restricted results.

Broad ANY and STAR selectors can retain arbitrary permitted descendants
up to the global run limit. An EXACT `Dp` rejects a strict descendant, so
this issue does not arise in that cell. At the same path, C5 performs its
existing tail meet. An ancestor correlated FLOW STAR can stay whole under
the current representability rule; any new cut must preserve that rule
for uncut pieces.

## 3. How it can reduce published work

Consider a raw result with many deep descendants under one new field:

```text
Dp:     p.[any]/T
Raw B:  {p.a.b.c.$/T, p.a.b.d.$/T, p.a.e.f.$/T, ...}
```

Current C5 retains the deep leaves. With the proposed cap, they can share
one published `p.a.[any]/T` DEMAND result. The existing publication store
can reject later equal capped memberships before notifying callers.
This can reduce both tree width and the number of fresh publication
updates, followed by fewer candidate scans and caller continuations.

The first new field is retained. This fits C2's one-field refinement
step: under `p.[any]/T`, the original deep fact emits a `p.a.*/T` initial;
the capped `p.a.[any]/T` fact also emits `p.a.*/T`. This is one important
cell to prove, not a complete equivalence proof for summary application,
reports, records, protection, or all demand tails.

The packed control retains 16 depth-3 leaves under current C5 and one
DEMAND prefix after the proposed depth-1 cut. This demonstrates possible
compression, without estimating how often it occurs in the projects.

The paired bound can advance. If the opposite run admits an initial at
`ret.f.[any]`, its field depth is 1. That initial becomes `Dp` when the
direction changes again, so the next publication cap can be 2 even when
the current producer's own premise remains a root point. This is why the
new rule does not impose the earlier permanent root-premise cap of 1.

The local wrap/unwrap control confirms this difference at global limit 2:
the preceding opposite initial has depth 1, the C5 output budget is 2,
the precise two-field publication remains NORMAL, and the other direction
can admit a depth-2 exact initial. This rescue does not need native replay.
The control uses production AP/C2/C5 operations, not a changed full driver.

## 4. What it does not reduce

C5 runs after the actor has built and stored its raw summary. The inverse
field-loop control constructs 255 raw leaves before C5 retains its single
exact endpoint. That output already satisfies this new bound. Its 1,281
processed items would not disappear from an output-only C5 change.

The new rule also leaves these costs:

- Reverse alias routes before C2 and repeated shared call stages.
- Scalarized reverse saved-record application.
- Native-record application and its repeated caller continuations.
- Long caller suffixes grafted onto a shallow template. For example,
  `ret.* -> p.left.*` applied to `ret.a.b/T` still produces
  `p.left.a.b/T`, before the ordinary caller field cut.

Conductor run-4's current-summary delivery is therefore a plausible target.
Stirling run-6/run-8 is dominated by direct reversed-call processing outside
saved replay; publication shortening alone does not explain how to remove
that principal cost.

The recordings do not include paired `Dp` depths or published fact paths.
We do not have a project count of the rows that this policy would cut.
Measure affected rows, memberships, candidate scans and downstream work
before claiming a project speedup.

The measured runtime stores raw NORMAL records before restriction. Under
the clarification above, new persisted NORMAL summaries must come from
the restricted admitted set. This can change record payloads and future
work, so the old raw-persistence probe is not a completeness proof for the
clarified design. The selected every-offer call replay policy is a separate
operation; no change to it is selected by this note.

## 5. Semantic and integration requirements

This is exact paired restriction followed by abstraction. Current C5
preserves the selected layer and relation pairs. A field cut can replace a
NORMAL precise fact with a broader ANY fact on DEMAND. That is a new
contract, with new soundness and alternating-progress obligations.

The implementation design must include all of the following:

1. Select a complete pair first. Its own `Dp` supplies the budget. Do not
   select an entry from one row and an exit or budget from another row.
   Retain the full current ND premise.
2. Use the existing cut semantics and protection transport. Keep marks,
   FLOW mark exclusions, and all uncut geometry and exclusions. A cut
   piece becomes ANY/DEMAND; a shorter NORMAL STAR is not an equivalent
   replacement for a correlated FLOW relation.
3. Restrict both NORMAL and DEMAND candidates before summary admission,
   propagation, and persistence. An unrestricted NORMAL candidate must not
   bypass this gate through the raw/native store. Review FLOW-backed
   replacement and native completeness against the admitted NORMAL set.
4. Classify outgoing demand from the admitted result. Currently
   `RunMethodAnalyzer.queuePublications` decides `selected` from the raw
   edge before C5. If a raw NORMAL edge is newly cut to DEMAND, that
   Boolean is false and the current code would omit the new refinement
   obligation from `summaries.addDemand` and the outgoing frontier.
   The intended rule needs no new per-edge handoff operation: the ordinary
   iteration barrier derives next-run demand from admitted DEMAND edges.
5. Review full-coverage early exit. Two compatible rows can have different
   caps. A row that retains an exact raw NORMAL result does not establish
   that a later row would add no new capped DEMAND result under a literal
   per-pair-union policy. Control-row early exit and run-2 static lookup
   shortcuts need the selected union/dominance rule and a new proof.
6. Treat typed ZERO and Target endpoints explicitly. They are not depth-0
   data facts. A ZERO current original can have a compatible DATA exit
   selector `Dp`; that data result can be capped. This proposal has no
   automatic ZERO-original exemption unless one is separately selected.

Do not reuse this boundary budget as an intra-procedural limit. A
root-to-root relation can need a two-field temporary in both directions,
even though both boundary depths are zero. The
[previous evaluation](bidirectional-premise-relative-field-limit-20261101.md)
contains that progress issue. Keeping the existing global body limit is
essential to distinguish the new hypothesis from the earlier one.

## 6. Evaluation result

Current C5 can exceed the proposed bound. The new policy is a plausible
way to reduce current-summary publication and caller amplification, and
it has a better refinement structure than a fixed current-premise cap.
It does not establish a bound on all facts processed in an iteration.

The next design should prove the projection against C2, paired C5,
handoff, restricted NORMAL persistence, FLOW-backed replacement, source
permissions, and Targets. It should measure excess depth relative to the
matched `Dp`, grouped by raw layer, tail and publication membership.
The actual overlap with the three slow runs remains unmeasured.

The code, receipts, and outputs for the three additional checks are in
[the intersection controls](data/bidirectional-demand-relative-intersection-controls-20261101.json).
The analyzer implementation is unchanged.

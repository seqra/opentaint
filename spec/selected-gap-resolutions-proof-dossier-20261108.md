# Selected gap resolutions: proof dossier

8 November 2026. This dossier covers the three changes selected for the
[combined spec](edge-subsumption-initial-emission-demand-intersection.md).
Use baseline `52829d5890ec3b3145cc996a1d8162d85cb8ceda`.
No production implementation is changed. Latest checked loop phase:
**run-5**. Latest checked cleaner phase: **run-3**. The Conductor example
now includes local **run-4/run-5** refinement and replay; it is not a new
project run.

**Finalized status:** no further unresolved FN-producing counterexample
is currently known for the reviewed FULL-mode cases. This dossier checks
local constructive witnesses; it does not claim a universal no-FN proof.
The remaining native/project and general-loop checks are acceptance work.
The Conductor-shaped example now has a checked NORMAL run-5 route.

## 1. Semantic scope

| Part | Previous proposal | Selected contract | Affected obligations |
| --- | --- | --- | --- |
| Protection storage/delivery | One OR-upgraded row with hidden plain coverage | Keep both exact classes; publish each fresh membership | P02, P04, P27, P32 |
| Partial selected cleaner | STAR/T, DEMAND, H survivor | ANY/T, DEMAND, H, Empty E conclusion; same premise | P31, P36 |
| Loop output | Own-ZERO DATA output could enter the growth gate | Own effective ZERO premise bypasses only that extra gate | P14-P15, P33-P35 |

These change retained work and refinement. They are not merely indexing
changes. Keep C2, paired C5, global field limits, field-action lowering,
complete ND execution, source permission, Target protocol and stopping.
The selected changes introduce no tail kind, mark, grounding label or
discarded-fact archive.

## 2. Separate protection classes

For geometry G, `(G,false)` and `(G,true)` have different logical keys.
Canonical insertion acts on one class only. If an old same-class edge
covers G, insertion and publication add nothing. Otherwise insert G in
that class, remove its covered same-class descendants and publish G with
its original flag. The other class is unchanged.

The constructive delivery argument is induction over the offered list.
For a covered offer, both producer and subscriber stay unchanged. For a
fresh offer, the subscriber receives that exact class and performs the
same insertion as the producer. Therefore equal initial canonical states
stay equal after every offer. This covers an arbitrary list in the
declared scalar geometry domain; it does not require an offer archive.

For the two exact orders the witnesses are:

```text
H then plain: publish (G,true), then (G,false); retain both.
plain then H: publish (G,false), then (G,true); retain both.
repeat either same-class membership: no further delivery.
```

The publication order can differ; the class coverage cannot. A plain
parent covers a plain child in either order. A protected-only parent
cannot cover that child. A pass sends each membership with the same flag.
It cannot create protection from a plain input.

[PlainCoverageDelivery](lean/proposals/subsumption-initial-demand-20261107/PlainCoverageDelivery.lean)
checks these statements constructively, including arbitrary input lists,
exact two-class identity, duplicate freshness, pass behavior and the
parent/child controls. Its geometry fixes the ordinary headers to the
existing MAY/T/DEMAND domain. Native packed trees, queue keys, mixed
marks, persistence and all-header subsumption remain implementation
correspondence checks. Do not implement the superseded OR renderer.

## 3. Selected partial cleaner survivor

Let an old selected PART result be `P -> x.p.*/T,D,H`. The old spatial
and E tests have already run. Replace its output with
`x.p.[any]/T,D,H,E={}`. The proof keeps the old input witness and its
output suffix. STAR required correlation of the two suffixes; ANY accepts
that same pair without the correlation requirement. Thus every old pair
has an explicit witness in the new relation. Clearing E only broadens this
already DEMAND result.

This is inclusion, not equality. Extra provisional pairs are permitted,
but they must not become NORMAL. The transformation keeps P, base, path,
mark, support and H. It maps old outputs and creates no output for a kill.
All NORMAL output results are unchanged. An already-EXACT BELOW survivor,
disjoint region, other mark, FLOW, existing MAY/MUST and RemoveAll branch
are outside the new guard.

[SelectedCleanerStarSurvivor](lean/proposals/subsumption-initial-demand-20261107/SelectedCleanerStarSurvivor.lean)
checks the generic guard and inclusion plus the E31 source/helper/sink
adapter. The finite catalog derives the real source permission and a
precise NORMAL backward summary in run-2. Saved opposite replay then
transports the actual marked child to the NORMAL sink in run-3. No
completion or guessed NORMAL provider is used. Native bulk masks, mixed
packets and field-action lowering still need integration checks.

The original
[CleanerMaySurvivorCandidate](lean/proposals/subsumption-initial-demand-20261107/CleanerMaySurvivorCandidate.lean)
is retained unchanged as the earlier narrow example. The selected generic
rule adds the explicit PART guard; do not apply the old example's blanket
root-only postprocessor to arbitrary disjoint STAR results.

## 4. Own-ZERO loop bypass

Apply normalization and paired C5 before publication. After application,
apply the ordinary global bound. If the effective local premise is ZERO,
retain that bounded result without the extra loop observation. DATA
premises keep the old growth test and restriction. Thus the bypass cannot
change their decision, even when their enclosing parent original is ZERO.

A ZERO input has no suffix to append. Repeating a fixed ZERO row produces
the same bounded geometry and support; boundary deduplication detects the
repeat. New DATA transformations can still grow suffixes and remain gated.
This gives no performance bound for all ZERO rows and no cross-run
convergence theorem.

[ZeroPremiseLoopBypassCandidate](lean/proposals/subsumption-initial-demand-20261107/ZeroPremiseLoopBypassCandidate.lean)
checks the selected rule. Its historical namespace is retained. The
reached run-2/run-3 repeat fixed points are unchanged in the model. The
run-5 source reaches the saved shrinking NORMAL reader, existing exact
admission and ordinary NORMAL sink. Global cuts stay DEMAND, an existing
DEMAND supply stays DEMAND, and the negative DATA-grower case still gates.

Eight [native component checks](lean/proposals/subsumption-initial-demand-20261107/native-zero-loop-bypass-candidate-20261108/receipt.json)
passed with a test-only policy adapter on the frozen baseline. They are
not a full redesigned iteration run. Reversed saved views must test the
effective premise, and runtime Boolean gate calls must receive that
decision. General DATA-row continuation and all physical ports remain
open obligations.

## 5. Conductor and remaining boundaries

The [Conductor example](conductor-must-admission-fact-trace-20261108.md)
shows why these three fixes do not close its MUST issue. That example has
no loop or cleaner and uses plain facts. Root ANY/FLOW demand selects a
field STAR/FLOW probe plus the exact FLOW prefix. A removed same-head
child ANY/FLOW demand selects MUST/FLOW instead. The stronger initial can
retain NORMAL uniform taint through a second field read; the two retained
coarse probes do not reproduce that operation.

[MustAdmissionAudit](lean/proposals/subsumption-initial-demand-20261107/MustAdmissionAudit.lean)
checks those C2/read cells. The small runnable historical example delays
the report from run-3 to run-5; it does not reproduce permanent loss. The
extended current-spec trace derives both B4 C5 outputs, the saved NORMAL
return reader and regenerated child guide. Native component checks confirm
MUST transport and the two F5 return classes. Full driver stopping remains
open because F5 can still contain a separate DEMAND summary. The
two real Conductor findings remain a separate recovery obligation.
No MUST-replacement or additive initial policy is selected here.

The selected rules resolve the three illustrated contracts within their
checked scope. They do not establish every native principal program,
project recovery, GROUP correctness or natural convergence. Native
integration must preserve both class memberships in one packet and both
arrival orders and must run the strict source/sink assertions.

## 6. Checked artifacts

The root-owned [receipt](lean/proposals/subsumption-initial-demand-20261107/component-checks-1209.json)
and [complete axiom audit](lean/proposals/subsumption-initial-demand-20261107/component-axioms-1209.txt)
check all pinned components, including the 44 selected-cleaner and 33
separate-delivery declarations. The ZERO component retains its preceding
11 checked statements. The checker rejects proof holes, custom axioms
and classical choice. Only `propext` and `Quot.sound` are allowed in the
printed dependency lists.

The package count includes historical and negative results. It is not a
whole-analyzer soundness count. Repeat the check with the documented
[manifest and runner](lean/proposals/subsumption-initial-demand-20261107/README.md).

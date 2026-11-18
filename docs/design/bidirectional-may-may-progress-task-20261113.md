# Working goal: termination of the MAY/MAY examples

Current consolidated documents:
[all known counterexamples](../reports/bidirectional-demand-termination-counterexamples-20261115.md)
and [the complete NE/progress approach](bidirectional-demand-termination-approach-20261115.md).
The chronology below remains historical evidence; withdrawn proposals are not
part of that consolidated approach.

Latest counterexample and resolution, 16 November:
[uniform saved reply](../reports/bidirectional-provisional-uniform-nontermination-20261116.md),
native **run-31**, with an uncapped recurrence proof under the latest exact
reply filter. Its remaining DEMAND MUST reply renews root Target after all
helper demand disappears. Both findings are already NORMAL. The current
consolidated proposal now unifies exact and uniform actual-reply support:
NORMAL absorbs only the identical concrete D value. The new uniform and
earlier exact references both stop at **run-7**, with findings and records
retained. The 18 earlier cold references keep their packets and stops,
latest **run-15**. [Current validation](../reports/bidirectional-definite-reply-support-20261116.md).

Previous exact-output counterexample:
[direct saved concrete MUST replay](../reports/bidirectional-provisional-must-nontermination-20261115.md),
native **run-31**, with an uncapped recurrence proof. Both reports are NORMAL
by run-5. After that the helper demand is empty, but saved-first provisional
replay keeps root `ZERO -> DemandTarget`. It uses ordinary conditional source
and observation rules, with no cleaner, pass, loop or recursion. No repair is
implemented. The consolidated proposal now handles this case with exact FULL
reply support absorption; the revised cold reference naturally stops at
**run-7**. The new proof also checks that all 18 earlier cold references keep
their reply packets and stopping results, latest **run-15**.

Updated 16 November 2026. User-selected replacement investigation. The demand
classification campaign stays paused. Follow [proof-guide.md](../../spec/proof-guide.md).

## Objective

Find and prove a bounded approach that makes every provided in-scope
example terminate without an iteration hard limit, including the nested-call
and ordinary pre/post-overwrite cases. Keep the old MAY/MAY
and ordinary global-cut cases, and add the protected concrete-T cleaner/
global-cut cycle. The current starting contract includes non-empty-MAY,
bounded refinement, NORMAL uniform FLOW coverage and the selected
MUST-preserving root-cleaner rule. None of those additions alone is a
complete solution to the new acceptance set.

Required examples:

- [Ordinary pre/post-overwrite saved-replay cycle](../reports/bidirectional-overwrite-saved-replay-nontermination-20261115.md): preserve real exclusions and the original raw query origins.
- [Nested and nontransparent call variants](../reports/bidirectional-prepared-child-saved-replay-20261115.md), including the complete Growth regression.
- [Method-only two-call cycle](../reports/bidirectional-non-empty-may-acyclic-nontermination-20261113.md).
- [BB version and enclosing-method cycle](../reports/bidirectional-non-empty-may-basic-block-retrace-20261113.md).
- [Ordinary double-read/double-write two-call cycle](../reports/bidirectional-bounded-refinement-ordinary-cycle-20261114.md).
- [Protected concrete-T cleaner/growth cycle](../reports/bidirectional-protected-cleaner-growth-nontermination-20261114.md): the same two-call helper, with root-only selected cleaning before its branches.
- [Uniform source/root cleaner](../reports/bidirectional-uniform-root-cleaner-nontermination-20261114.md#10-selected-must-preserving-revision): keep the selected MUST-preserving run-1 completion as a regression.
- The wrapper/child-demand case and exact-root selected-cleaner survivor
  are required finding-preservation regressions. Their existing nonempty
  query and concrete repair routes must remain available.

Keep all these examples in the acceptance set. Solving the protected
concrete case does not replace the old method-only, BB or neutral ordinary
case. The uniform-root example is tested under the updated cleaner rule,
not reused as a counterexample under its withdrawn old rule. The special
`AnyField` pass-target example is outside this goal's required set; do not
claim that solving the ordinary examples proves termination for that model.

| Required case | Original failure | Required result |
| --- | --- | --- |
| Method-only, read `p.f.g`, write `ret.f` | Root MAY/MAY renewal | Finite complete frontier and preserved NORMAL finding |
| Same program with separate read/write blocks | Relative C5 cuts and reverse-MUST guidance | Finite frontier including all inner blocks, preserved finding |
| Longer-reader/bootstrap variant | Required reader not initially NORMAL | Derive its provider; do not assume it is already present |
| Ordinary read `x.f.f`, write `ret.f.f`, two calls | Near-limit queries create new global NE cuts forever | Stop the recurrence, including root Target demand, without relaxing field limits |
| Same two-call helper with selected root cleaning | Protected concrete-T cuts bypass neutral FLOW coverage; DemandTarget repeats even with a NORMAL finding | Empty complete refinement frontier, retained finding, no protected-to-plain replacement |
| Uniform source and same-head root-only cleaner | Old partial MUST demotion caused repetition | Keep the selected MUST-preserving completion at run-1; introduce no further cleaner change |
| Wrapper/child-demand regression | Coarse caller input can starve a needed child | Preserve source permissions and the finding |
| Selected root cleaner with marked descendant | EXACT-only admission loses the surviving child | Preserve nonempty repair and the finding |

Every new forward iteration must advance effective precision. Repeated
work can be removed only with a redundancy proof that preserves eventual
precise findings. If infinitely many refinements are needed, a finding
must not remain supported forever by the same unresolved approximation.
Normal means the existing AP contract, not a claim of concrete JVM path
feasibility beyond that contract.

## Boundaries

- Respect method and block abstraction. Do not compose full untruncated
  evidence across calls or perform a parallel field-sensitive analysis.
- Do not use backward MUST sink seeds: summary reversal is not valid by
  merely swapping the resulting uniform premises and conclusions.
- Do not revive field bans or implicit weak writes.
- Keep the existing no-MAY-owned-premise requirement and avoid replacement
  tail tokens such as STAR-or-ANY. Proposed changes to an earlier selected
  admission rule must be explicit and reviewed.
- Do not use the run-11 cutoff, future-run observations or JVM types as a
  redundancy certificate. A stable count is not a proof of convergence.
- Preserve the selected MUST cleaner rule, real field cuts and literal
  protection classes. A protected provider must retain its protection;
  do not erase H, merge plain/protected membership or silently generalize
  FLOW backing to protected concrete facts.
- The selected MUST cleaner rule already has the documented exact-root
  NORMAL false-positive consequence under the old concrete cleaner
  meaning. Do not hide it or change that decision during this task.
- Leave production implementation unchanged until an approach is selected.

## Investigation order

1. Pin the exact MAY/MAY C2 outputs and complete paired C5 rows. Identify
   why the next forward run repeats the same question.
2. Test small bounded alternatives. Cover empty and nonempty suffixes,
   selected cleaners, concrete/FLOW lanes and saved NORMAL replay. An
   EXACT-only answer is a candidate to test, not an accepted fix.
3. Check producer-side precision loss too: creating the submitted MAY
   unnecessarily can be the root cause of the admission repetition.
4. Trace sink seeds, source permissions and ZERO/Target guidance. Forward
   non-exact matching and backward non-exact seeding are different questions.
5. Prove a bounded refinement or retirement algorithm and retrace all
   required examples uncapped. Repetition must disappear, not move to an
   equivalent row or another summarizable block.
6. For the protected case, check concrete and FLOW/mx query families,
   the extra NORMAL exact results, saved-record replay and the second
   call's complete admitted family. Removing the four old cut witnesses
   alone is not a complete convergence check.

## Completion evidence

Give an executable algorithm with storage, guards and before/after behavior.
Supply constructive Lean proofs for the modeled changes and clear traces:
demands, submitted facts, initials and NORMAL/DEMAND summaries for each
relevant method/block and run. Bind native component tests where applicable.
State remaining proof scope honestly; mathematical identities alone do
not establish native finding preservation, bounded cost or termination.

Do not mark this goal achieved because a cycle witness fails to derive.
Show the actual post-change frontier, preserved findings and natural stop.
An invariant that removes only the original cycle witnesses is insufficient:
check both double-write/global-cut families and all extra paired rows too.
Retain the independent sink/source permissions and NORMAL finding route.
Record the latest reached iteration separately for native components,
formal reference execution and project runs.

## Starting state

The selected [non-empty-MAY reference](../../spec/non-empty-may.md) maps
same-head MAY/MAY to EXACT and STAR starts, plus the applicable companions.
The root query family is independent of the later field-limit increases;
`AcyclicMayCycle.second_call_commands` checks that repeating family for
arbitrary later run indices and positive limits.

The full relational evidence design is
[withdrawn](bidirectional-relational-loss-evidence-proposal-20261113.md).
Its models remain historical reference components, not the active approach.
The current-code MarkCheckTest and Run1SinkProjectionTest passed all 12
tests in the sink check. This validates current matching/coexistence only,
not a new non-empty-MAY implementation or its termination.

No new project scan was made. Historical reached/completed/accepted forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**,
Stirling-PDF **run-11/10/9**.

## Investigation result, 14 November

The [bounded guard-partition investigation](../reports/bidirectional-may-may-progress-investigation-20261114.md)
gives an executable candidate and 38 new constructive Lean claims.
From the traced run-4 NORMAL basis, the method-only and BB-method references
preserve the finding and naturally stop after run-5. EXACT-only admission
fails the cleaner check. Production and the selected spec are unchanged.
Native integration and a general MAY/MAY progress guarantee remain open;
this scoped result does not complete those obligations. A longer-reader
example exposes a guard-bootstrap limit. Retaining bounded cut prefixes
as query guards is the next design direction; its local progress lemma
does not yet prove global/native progress.

## Replacement approach, 14 November

[Bounded demand refinement](bidirectional-bounded-demand-refinement-20261114.md)
keeps the original global and `FL(Dp)+1` conclusion cuts and the original
`FL(Dc)+1` initial bound. It replaces full NORMAL-guard expansion with one
observed field level per existing demand row, in both directions. Deeper
post-C5 demand heads survive semantic MAY union; explicit possible bindings
prevent a guessed refinement from confirming a NORMAL Target.

The closed method-only reference now derives its NORMAL reader from the
run-1 writer and revised run-2 plan. It does not assume that reader at
run-4. The BB trace includes the conservative reverse-MUST replay. Both
preserve the finding and naturally stop after run-5; the real run-3 global
cut and its DemandTarget are retained. The revised plan keeps G local;
it no longer puts an artificial exclusion on a fact or summary. Complete
child-query coverage is required before coarse work can be delegated.
The proof package has 90 new checks, 199 with dependencies. Production and the selected non-empty-MAY spec are
unchanged; the approach is ready for semantic review and native binding.

## Remaining counterexample, 14 November

The [intrinsic-MAY root trace](../reports/bidirectional-bounded-refinement-acyclic-nontermination-20261114.md)
is a checked counterexample under the latest bounded proposal too. A
permitted pass rule with an `AnyField` target produces MAY/DEMAND from an
exact source. Each backward run renews the exact source permission, and
every handoff retains `ZERO -> DemandTarget, DEMAND`. There is one
straight-line analyzable block, no loop or recursion, and no field cut.
The uncapped induction has 21 new Lean claims, 220 with dependencies.
This is a limitation of the permitted rule language, not a regression of
the earlier ordinary-field reference which finishes at run-5.

## Ordinary-code counterexample, 14 November

The user excludes special pass rules. The
[double-read/double-write trace](../reports/bidirectional-bounded-refinement-ordinary-cycle-20261114.md)
uses only ordinary code and whole-object source/sink rules. Near-limit
MUST/STAR queries generate global NE cuts before the proposed NORMAL
precoverage. The two calls and their backward dual continually admit the
next deeper query. Helper DATA heads move deeper, while the root's same
`ZERO -> DemandTarget, DEMAND` repeats without a hard limit. The Lean
induction passes: 42 new theorems, 241 with dependencies. An exploratory
reference still has demand after run-31; no new project scan was made.

## Scoped approach found, 14 November

[NORMAL uniform FLOW coverage of NE](bidirectional-normal-uniform-ne-coverage-20261114.md)
adds a conservative same-complete-premise egress rule to bounded refinement.
A legally admitted NORMAL uniform FLOW output covers a DEMAND NE output
in its region. Keep the real field cuts; do not retain full suffix evidence
or add an artificial field exclusion. A retained NORMAL record can supply
a transient legal uniform view when earlier precoverage omitted its
duplicate summary.

The [checked traces](../reports/bidirectional-uniform-ne-coverage-reference-20261114.md)
retain the complete acceptance set above. The old method-only and BB cases
and the new ordinary two-call case have empty reference frontiers at
**run-3**, with their NORMAL findings preserved. The longer-reader,
wrapper and protected selected-cleaner routes remain available. Both calls
and all relevant paired rows are evaluated; this result does not merely
remove the previously observed cycle witness.

The proof checker passes **51 new declarations, 292 including dependencies,
in 17 modules**. Eleven existing native mechanism tests also pass. Those
tests establish reuse of existing MUST handling, not implementation of the
new NE law. The exploratory ordinary baseline still reaches **run-31**;
the new scoped references stop naturally at **run-3**, without a hard cap.

This completes the scoped approach investigation for the provided positive
field-transfer references. It does not prove universal termination or full
native service correspondence. Production and the selected non-empty-MAY
spec remain unchanged. Native activation requires the complete qualified
service checks stated in the proposal; unsupported cases retain current
behavior. The separate special-pass counterexample remains outside scope.

## Next counterexample search, 14 November

The next user-selected goal is to find another uncapped termination
counterexample under all three pieces: non-empty-MAY, bounded refinement
and NORMAL uniform NE coverage. Keep the old acceptance cases. The new
example must have no loops, recursion or special pass rules.

The [uniform-source exact-root cleaner counterexample](../reports/bidirectional-uniform-root-cleaner-nontermination-20261114.md)
meets these constraints. One root block executes a whole-object source,
a selected root-only T cleaner, and a whole-object T sink. The source's
MUST loses NORMAL support at the partial cleaner. Backward MAY survives
that cleaner and renews the source permission. Every forward/backward
handoff contains the same `ZERO -> DemandTarget`, with no field cut or
DATA initial to refine.

The native reproduction reaches **run-21** with exactly one repeated
DemandTarget, zero DATA method summaries, no NormalTarget, and only ZERO
premises. All processed explicit field chains have length zero. Five new
tests and five earlier cleaner tests pass. The constructive induction
proves non-termination without any iteration limit: **20 new claims,
312 with dependencies, 18 modules**. The earlier coverage rule and all
required old/new regressions are rechecked by the same proof command.

This closes the renewed counterexample search. The earlier scoped coverage
result remains valid; it did not cover this preserved concrete partial
cleaner behavior. No production fix or semantic revision is selected here.

## Cleaner decision after the counterexample

The user then selected a change: an EXACT-reach selected T cleaner cannot
clean a concrete MUST/T at the same base and path. Preserve its input
layer and existing survivor protection. The [updated specification](../../spec/non-empty-may.md)
pins this scope; the [revised trace](../reports/bidirectional-uniform-root-cleaner-nontermination-20261114.md#10-selected-must-preserving-revision)
stops at **run-1**, so the cleaner case is withdrawn as a counterexample
under this new contract. The old native **run-21** evidence remains valid
only for unchanged production.

The revision also permits a NORMAL exact-root false positive under the
old concrete cleaning meaning. This consequence is explicit, and is
checked along with layer preservation and run-1 completion in 9 new
constructive claims. No universal termination or old-contract precision
claim follows from closing this example. Production is unchanged.

## Counterexample under the MUST-preserving rule

The resumed search finds a [protected concrete cleaner/growth cycle](../reports/bidirectional-protected-cleaner-growth-nontermination-20261114.md).
Put the ordinary root-only selected T cleaner before the two branches of
the read-ff/write-ff helper, and call that helper twice. Source and sink
remain ordinary whole-object rules. There are no loops, recursion or pass
rules. The selected MUST-preserving decision is retained and rechecked.

Recurring facts have known nonempty paths, so the cleaner is disjoint:
it preserves their layers and adds the existing protection. Two field
operations then create real global cuts in concrete T relations. They
are outside the new neutral, unprotected FLOW-to-NE coverage rule. Both
actual call bindings and the reverse source hit are recomputed. The root's
same `ZERO -> DemandTarget` repeats after **run-3**, **run-5**, and every
later forward run. A NORMAL finding can already exist in run-3; it does
not erase this separate anonymous DEMAND terminal.

The constructive checker passes **38 new claims, 359 with dependencies,
21 modules**. Its induction is uncapped and permits same-head MAY/NE
coalescing independently in every run. A finite witness replay reaches
**run-31**. Four native component/bootstrap tests pass, including a real
**run-3** helper C2/body/C5 analysis; the new NE tail is not implemented,
so these are component checks, not a whole-engine new-policy run-31.

This fulfills the renewed counterexample goal. All earlier reference
proofs and the MUST-preserving revision are rechecked by the same command.
No production fix or additional subsumption/cleaner policy is selected.

## Current active goal: termination approach for the combined acceptance set

The user has changed the goal from counterexample search back to approach
design. The protected concrete cycle is now a required failing input,
alongside all old examples listed at the start of this document. Historical
completion claims above describe their earlier, smaller acceptance sets.

The new result must give an executable bounded algorithm, constructive
finding-preservation and retirement arguments, and complete post-change
frontiers for the required methods and blocks. It must retain truncation
and the selected cleaner behavior, and must not rely on an iteration cap
or composing full suffix evidence through calls. Every major change in
mark/protection coverage, matching or handoff must be explicit. Production
remains unchanged while this approach is investigated.


## Enlarged acceptance set: approach found, 14 November

[Same-lane uniform coverage and complete reply packets](bidirectional-same-lane-uniform-termination-20261114.md)
addresses the protected concrete-T case as well as every older in-scope
example. This is a proposed semantic extension, not a production change:
a same-H NORMAL MUST provider can retire a same-T NE demand under the
identical complete MUST original. Equal FLOW output mx is also allowed.
Protection is retained; no plain/protected replacement occurs.

The accompanying delivery rule folds one complete publication/replay
packet with existing MUST/MUST canonicalization before admitting the
next call. The model proves that omitting this step can create a stale
STAR/DEMAND query even after the initial MUST cuts are covered. This
requirement is explicit; final-store canonicalization alone is insufficient.

The full new run-3 packet has 15 cold rows (10 NORMAL, 5 DEMAND). All five
cuts have legal NORMAL providers. Exact-root replies are kept and their
extra C2 family is evaluated: it adds one NORMAL FLOW/mx row. The closed
basis has 11 NORMAL rows and no demand. Both calls have the same NORMAL
EXACT/MUST actual basis, and induction proves every further delivery round
unchanged. Main retains its NORMAL finding and has no outgoing demand.
The old method/BB/neutral references also finish run-3; standalone selected
MUST cleaning still finishes run-1. Finding regressions and warm providers
are rechecked.

Fresh proof receipt: **401 audited declarations in 25 modules, 42 new
claims**. Native provider/application validation: **15 tests passed**,
including three new tests. [Per-run annotations and the complete basis](../reports/bidirectional-same-lane-uniform-termination-reference-20261114.md)
separate reference completion at **run-3**, native body components at
**run-3**, and unchanged historical project positions. No hard cap or
full-suffix evidence is used.

This completes the approach search for this acceptance set. Production
activation, wider alias/rule/native correspondence and universal program
termination are separate work. No claim is made for the excluded special
pass-target example.


## Active replacement goal: next cleaner-free counterexample

After the approach above, the user requests another termination
counterexample with no loops, recursion, special pass rules or cleaner
rules. Work until there is a code example and a constructive uncapped
proof. Preserve the current approach and keep production unchanged.

[Search record](../reports/bidirectional-no-cleaner-counterexample-search-20261114.md)
and [accepted nested-call example](../reports/bidirectional-nested-saved-replay-nontermination-20261115.md).
The completed search uses only fully analyzed ordinary code and the two
configured marking/observation rules. Saved NORMAL replay is unchanged.
There are no loops, recursion, cleaners, special pass rules or library-MAY
model. A wrapper around a read-two/write-two helper regenerates four paired
FLOW/MAY demand rows indefinitely. The actual producer marks only x.f.g;
first-field admission starts x.f.STAR and the saved opposite reader
recreates MAY without retaining the known g distinction.

Cold runs **run-1 through run-9** are checked from empty stores. Complete
stationary **run-9/run-10** packets and caller/Target closure give an uncapped
induction. The exploratory capture reaches **run-31**. The checker passes
**69 new theorems, 542 audited declarations in 32 modules**. Three native
operator tests pass; field limit 8 is run-9 geometry, not an integrated NE
engine completion. Production is unchanged and no new project scan was run.

This completes this replacement goal. The earlier approach remains a
completed result for its old acceptance set, not a universal termination
proof. No further replay-pruning or admission-policy change is selected.


## Current result: old and new acceptance set, 15 November

The user changed the goal back to an approach for the old required cases
and the new nested-call example. The selected preceding mechanisms stay:
non-empty MAY, bounded local plans, same-H uniform coverage, complete reply
folding and the MUST-preserving cleaner rule. The classification campaign
remains paused.

The [new proposal](bidirectional-transparent-forwarder-termination-20261115.md)
shares the analysis owner for certified pure forwarding methods. This is an
explicit analysis-semantic change: such a method no longer applies its own
C2/C5 before/after its sole call. Its original bounded actual is given to the
original inner call's canonical owner; the logical facade/trace frame stays.
No method with fields, rules, handlers, ambiguous targets or an unsupported
adapter is treated as transparent. No raw field evidence is composed.

The [complete reference report](../reports/bidirectional-transparent-forwarder-termination-reference-20261115.md)
contains all new cold annotations. It derives the callee NORMAL records
rather than assuming them. The helper DATA frontier closes at run-6, but
entry's real field-cut Target keeps the analysis running through run-7 and
run-8. At **run-9**, DATA and Target demand are both empty and the NORMAL
observation remains. All old required references retain their run-1/run-3
closures or their legal NORMAL observation/repair routes.

Constructive validation: **55 new theorems, 597 audited declarations across
36 modules**. Native services: **12 component tests passed**, including
three new precise-replay/layer/backward-route tests. The old-policy control
still reaches run-31 with an uncapped recurrence proof. The new reference
naturally completes run-9; no hard iteration limit is used. No project scan
was run and production is unchanged.

This completes the approach for this acceptance set. It is not a universal
termination proof, a general inside-result pruning rule or a verified JIR
classifier implementation. The proposal states the recognition and
context/port/trace adapter obligations before native activation. No further
field, cleaner, mark or Target semantic change is selected.


## Replacement investigation: persistent input partitions, 15 November

The user rejected transparent-forwarder owner sharing as too dependent on
the sample's code shape. Its completed proofs remain historical, not the
active solution. The demand-elimination campaign stays paused.

The [replacement proposal](bidirectional-progressive-input-partition-20261115.md)
keeps separate method/block owners and uses a persistent, budgeted input
partition. Supported ordinary reads and saved NORMAL reader applications
use the same complete child-service cover. At most one observed missing
trie edge is installed per owner and direction at a handoff. Paired output
restriction, actual replay, truncation and all selected older coverage
mechanisms remain in force. No full suffix evidence is composed across calls.

The proof and full-state reference results are recorded in the
[report](../reports/bidirectional-progressive-input-partition-20261115.md).
This changes local entry permissions and owned-query routing explicitly;
it is not a technical-only optimization. Production remains unchanged.


## Active goal: avoid whole-body refinement amplification

The user identified the main cost risk in persistent input partitions:
refining an input can multiply unrelated body work, publications and caller
processing. A new ordinary-code reference confirms 2 versus 18 executable
summary memberships at run-8, 13 versus 29 callee inputs, and identical
outer packets. Both controls naturally complete at run-11. The one-edge
metadata bound is not a propagation bound.

The user resumed the approach search. Keep the old required examples, the
nested/nontransparent references and this growth case as regressions. Test
refinement at the operation which loses suffix information, without starting
refined hypotheses at method entry or reoffering them to the callee. Do not
claim a workload bound from a bound on trie nodes. Production remains
unchanged; the campaign remains paused.


## Selected replacement: reuse prepared children for saved replay

The expanded investigation found that the existing child families suffice.
Dynamic local origins were unused in all required fixtures; creating them
and a persistent trie is unnecessary. Full-guard composition was also
rejected after a run-6 summary increase from 2 to 17 in the two-inner-call
reference.

The [new proposal](bidirectional-prepared-child-saved-replay-20261115.md)
only routes supported owned saved-NORMAL contributions through already
prepared children, under a stable per-query cover. C2, C5, raw initial keys,
field transfers, original call offers and current-summary matching remain
unchanged. The native gate must establish every potential consumer's
complete child service before processing a deduplicated initial.

The [report](../reports/bidirectional-prepared-child-saved-replay-20261115.md)
records the complete references and the cost scope. The old and new growth
case states are equal at every run-1 through run-11. The new nested and
nontransparent positive references naturally finish by run-15. A filter-only
fixed-plan bound is proved; it is not a bound on all future iterations'
scalar fact counts. The post-read screen has a largest total membership
increase of 3.6%, so no global zero-growth claim is made.

Production is unchanged. The paired-demand/native-adapter and unsupported
service limitations remain explicit. The classification campaign is paused.

## Counterexample after ordinary overwrites

The resumed search found a counterexample to universal termination of the
selected prepared-child saved-replay approach. Ordinary `x.g = new Node()`
before the branch and `y.g = new Node()` after it put real `{g}` exclusions
on both derived NORMAL records. The selected routing requires empty real
exclusions, so the wrapper continues to publish four MAY demand rows.

The [complete report](../reports/bidirectional-overwrite-saved-replay-nontermination-20261115.md)
contains cold run-1 through run-13 traces and the uncapped recurrence proof.
Latest finite reference: **run-61**. The proof checks all later limits and
includes actual caller offers, producer permission and fresh ZERO/Target
continuation. It uses no hard iteration limit. There are no loops,
recursion, cleaners, special pass rules, statics or unresolved transfer models.

An audit strengthened the reference's NORMAL duplicate check to use its
complete E-aware image. That removes a redundant fifth writer-cut row;
the four MAY rows still repeat. Thus the result does not depend on that
model artifact. The closed return-cone proof derives the two records from
ordinary field transfers, and four native tests check the decisive operators.
Validation: 88 new theorems, 998 audited declarations, 64 modules.

The counterexample goal is complete. No new repair is selected or implemented.
Production is unchanged; the classification campaign remains paused.

## Approach for all supplied references, 15 November

The [exclusion-aware child-cover approach](bidirectional-exclusion-aware-child-replay-20261115.md)
keeps the existing C2 families and frozen complete child service. It removes
only the three empty-field-E gates on a matched operand and its NORMAL
record. Real E is still checked by native matching at its original scope;
no parent exclusion is rebased onto a deeper initial. There is no new query,
caller offer, partition, larger budget or full evidence composition.

The new ordinary-overwrite case naturally finishes at **run-9**. All twelve
complete required reference executions naturally finish at **run-3 through
run-15**, with expected observations and empty DATA plus Target demand.
The Growth regression's complete old/new states match at every run-1 through
run-11. Earlier selected cleaner/protection packages remain checked
compatibility dependencies. Structured diagnostics reach **run-19**.

The [report](../reports/bidirectional-exclusion-aware-child-replay-20261115.md)
contains the full new principal trace, before/after work, negative cases and
proof/native scope. A 400-case E-heavy screen has no new observed finding
regression and a largest equal-prefix summary-membership ratio of 1.042.
Another 116 structured variants all naturally finish; five old-mode runs
remain unresolved at the diagnostic run-41 horizon. Those finite survivors
are not additional non-termination proofs.

One independent-concrete-model mismatch occurs in both old and new modes,
with identical observed work. It is documented as an unchanged baseline
reference-alignment gap. The local prefix theorem is not a whole-core native
simulation or universal termination proof. Native integration still must
bind the existing frozen child service to actual aliases, rules and ports.
Production is unchanged. The classification campaign remains paused.

## Next counterexample: EXACT-origin ordinary nested writes, 15 November

The resumed search found a synthetic core-form counterexample to the latest
exclusion-aware approach. A nested ordinary `write(x,[f,g],strong)` can promote
an EXACT/FLOW prefix probe to MAY. The current prepared-child routing covers
STAR contributions and therefore leaves this contribution active. One helper
and one call suffice; no loop, recursion, cleaner, pass rule or unresolved
transfer is used.

The [report](../reports/bidirectional-nested-write-nontermination-20261115.md)
embeds the code, requested annotations and uncapped proof. Latest finite
reference: **run-61**. The complete cold reference is checked through
**run-11**; the same root MAY obligation is renewed at every later forward
run. The proof includes backward producer permission and fresh anonymous
ZERO/Target guidance. Validation: **90 new theorems, 1,487 audited declarations,
85 modules**, plus **4 native operator tests**.

The scope is the supported synthetic nested-write core form. It is not an
end-to-end JVM-front-end reproduction: the JVM adapter normally lowers local
field writes to one accessor and temporary registers. No whole-production
simulation theorem is claimed. The concrete supplied g region produces no
marked return in either branch. Production is unchanged, and no repair is
selected by this counterexample result. The classification campaign stays
paused.

## Replacement approach: point semantics at identity keeps, 15 November

The [new approach](bidirectional-exact-point-write-progress-20261115.md)
removes one raw transfer exception: an EXACT/FLOW point no longer enters a
strictly deeper excluded identity keep. The actual point still gets the
existing same-head/ancestor NORMAL keep and its real exclusions. Ordinary
value writes, STAR uncertainty, concrete marks, MUST, prepared child routing,
C2/C5 and ZERO/Target rules remain unchanged. This is an explicit semantic
correction to the field-transfer case, not a storage optimization.

It adds no child query, field ban, evidence store, partition, origin or
full-path composition. The root point query remains in the admission family.
Its impossible descendant contribution is omitted by point geometry; this
does not require the child-cover assumption used for STAR routing.

The new negative counterexample stops naturally at **run-3**. Five positive
nested-write variants retain their observations and stop at **run-3, run-5
or run-11**. All twelve previous reference executions have exactly equal
old/new states; their latest natural stop is **run-15**. The
[report](../reports/bidirectional-exact-point-write-progress-20261115.md)
includes the cold trace, actual caller/Target behavior, work and limitations.

Validation: **596 new theorems, 2,083 audited declarations, 105 modules**;
**5 candidate native checks and 4 original controls passed**. A 1,000-case
diagnostic naturally finishes by **run-13** in the new mode, with no loss of
an old NORMAL result. One independent-region/reference mismatch is unchanged
in both modes, including complete states, and is documented explicitly.

This establishes the supplied synthetic references and the local point
correction. It does not establish universal whole-core termination or a
Java-front-end reproduction. Production is unchanged. No implementation
or additional repair is selected here; the classification campaign stays
paused.

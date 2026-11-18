# Next iteration after demand refinement

The revised FULL diagnostic policy completed OWASP through run-11.
Conductor stopped at the memory guard in run-2, ThingsBoard at the
guard in run-1, and Stirling-PDF at the timeout in run-4. The current
ranking puts the earliest new resource failure first. Conductor's
previous analyzer completed run-2 in 41.308 s and reached run-8
with the same limit and heap. Its revised run-2 point-fact
memberships are 77.0% static. Standing caller values retain 1.13 GB.
[Measurements](../reports/bidirectional-demand-refinement-performance-20261118.md)

## 1. Limit the R32 relay on shared static carry

**Current.** R32 turns a same-head run-2 STAR offer into a STAR
identity. A concrete selector produces a concrete DEMAND start
and a NORMAL FLOW companion. Shared carry creates a matching
selector at every offered static slot. In Conductor, 99.78% of
instrumented same-head STAR offers came through this route.
Restoring the prior EXACT start for shared carry alone let
run-2 finish in 183.584 s under the same heap. The diagnostic
offered 57.2% fewer initial keys and created 46.5% fewer caller
groups than the revised scan had recorded at abort.
[Rule isolation](../reports/bidirectional-demand-refinement-performance-20261118.md#conductor-rule-isolation)

**Proposed.** Verify the carry-only change first. Use the
previous EXACT start when the same-head STAR selector comes
only from shared carry. Keep R32 for explicit and virtual pairs,
and keep the deeper relay. Restore the STAR route where a
static suffix needs it and an admitted explicit or virtual pair
or saved NORMAL transfer supplies no equivalent service.
Use the same carry distinction in C2 and raw C5. An explicit
pair and a synthetic one can have equal endpoints, so preserve
the explicit witness until C5 establishes its coverage. Keep
the current saved-first replay and physical boundary ports.

**Expected effect.** Reduce the number of concrete static starts
and standing caller groups. Check the allocated support by layer,
not just the number of explicit H1 pairs. Require the overwrite
and nested-wrapper relay controls, concrete static read/write
controls, and the run-2 memory and finding comparison before
activating a narrower rule.

## 2. Share identical qualified replies

**Current.** A public summary delta and each qualified copy
enter separate publication paths. An input can match several
qualifiers that select the same effective operand.
Conductor run-2 retained 448,592 qualified FLOW/TAINT
memberships beside 449,452 ordinary DATA memberships.
Disabling qualified replies for diagnosis completed run-2
in 98.344 s and lowered `decide` publications from 133,031
at abort to 19,758 at completion. It also changed the outgoing
guidance. [Rule isolation](../reports/bidirectional-demand-refinement-performance-20261118.md#conductor-rule-isolation)

**Proposed.** Share the admitted payload across qualifications that
use the same full premise and physical port. Keep each qualification
that can authorize a binding. Find all qualifications that match an
input delta, then apply the result once per distinct effective operand.
Keep a late qualifier's delivery if it authorizes a new operand.

```text
for row in matchingCurrentRows(input):
    for matchedOperand in distinctEffectiveOperands(input, row.qualifiers):
        deliver(row.port, input.completeOriginal, row.premise, matchedOperand, row.payload)
```

A distinct delivery key includes the complete original, recipient
and port, premise arm, effective operand, layer, masks, protection
and admitted payload. Keep the existing complete ND join. For
Target, keep the typed target and exact report ID. Public and
qualified deliveries can share work only when their effective
application and all callbacks agree. A revised publication can
be used by a later caller, so keep the standing matching
capability until the current index is released.

Reject an auxiliary possible qualifier for a concrete named
static selector at its own head. For `Dc=C.f.MAY/T` or
`C.f.NE/T` and a raw start at `C.f`, that qualifier would need
a concrete STAR actual at a strict prefix of `C.f`. The static
grammar permits an EXACT class marker at `C` and requires a
named field for concrete STAR. A prepared child has a new
field, so it also cannot create a possible command at the same
head. Keep the admitted ordinary publication. The guard applies
when the raw start is a FLOW companion of that concrete selector.

**Expected effect.** Reduce payload copies and repeated
application work while preserving every distinct effect.
Count exact effective deliveries, redundant qualifying matches
and impossible qualifiers. Require exact H2 and observation
parity with the revised policy. The entire diagnostic removal
quantifies activity in this path. It does not give a savings
estimate for sharing identical applications.

## 3. End run-2 static searches after complete service

Start with the Conductor attribution controls. Keep the same H1
when testing run-2 changes. Change one of same-head STAR admission,
virtual mapped FLOW companion lookup, or qualified delivery at a
time. Record actual emitted starts, public and qualified rows,
caller memberships and static states through run-2. Disable a
service only in a diagnostic checkout. A diagnostic completion
identifies work attributable to the change. Rule adoption still
requires the corresponding reachability evidence.

**Current.** Revised C2 collects explicit and shared carry commands.
It then opens a separate accumulator for virtual static entry searches.
The accumulator can require an entry and actual pair even if the
explicit rows already supply all ordinary starts for that pair.
Revised C5 traverses the static completion for each offered summary.
In Conductor run-2, the engine visited 4.53 million static C2 states and
9.45 million C5 states before the guard stopped it. It recorded 50.54
million owner-bit queries. The global field limit was one.
[C2 and C5 lookup](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/store/DemandStore.kt)

**Proposed.** Use two exact coverage sets in one query. Seed ordinary
coverage from explicit and shared carry results. Observe every
qualified obligation that can affect delivery. Stop a static search
when both sets are covered, or when all reachable candidates were
checked. Use the static envelope indexes to find the obligations.

```text
ordinary = exact starts already supplied by explicit and carry rows
possible = exact bound commands already supplied by matching routes
for reachable static result in lookup order:
    install missing ordinary starts
    install missing qualified possible commands
    if every required ordinary start and possible command is supplied:
        stop the lookup
```

A required start includes its raw initial and support. Use the same
producer for the complete family in both the coverage setup and the
rightmost target lookup. Include companions and eligible saved-guard
children. A possible command also includes the entry projection,
caller actual, physical owner route and bound support. An explicit
qualification and a virtual qualification use separate match keys.
An uncertain envelope posting stays required until a complete view
can discharge it. Keep exhaustive C5 enumeration in the first
change. Removing a C5 visit requires coverage of the same qualified
paired row, budget and admitted packet. Use the typed terminal views
for Target and ZERO.

**Expected effect.** Avoid graph searches that cannot add a start or
deliver a new binding. Count avoided states, applicable candidates and
owner checks before attributing any heap savings. Compare exact command,
bound-delivery and paired-output sets against the current revised
implementation. Include real run-2 static and backward ZERO routes.

In the same regression tests, compare standing caller values and
the joined point-set size at a matched run-2 milestone. A shorter
search can reduce CPU while leaving the same fact set and memory
pressure. The largest retained point shape in Conductor is a
static `STAR/T,DEMAND` result. Test each admission change against
that shape as well as aggregate heap use.

## 4. Reject impossible prefix cuts before saved replay

**Current.** A growing loop output tests shorter packets. Under
revised demand refinement, the early admission probe returns
`Unsupported` and each trial constructs a full observation.
That observation includes saved adjacent replay and enclosing C5
even when an admission difference is sufficient to reject the
trial. In Stirling-PDF run-3, 53.68% of the samples in a
30-second CPU window include `LoopOutputRestriction`, 57.22%
include `LocalRelationApplication`, and 30.10% include revised
C5. That run took 418.955 engine seconds. Two contexts for
`EmlProcessingUtils#decodeMimeHeader` made 524,384 prefix trials
and 1,455,858 complete observations. The same path accounts for
59.32% inclusive loop restriction in the run-4 near-timeout CPU
window. The two contexts made 1,455,814 C5 queries during run-4
and published 33 local rows before the abort.
[Loop observation code](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/MethodBlockRuntime.kt)

**Proposed.** First build the existing revised admission bundle
once per trial. Force both routes and compare its complete label set
with the raw observation. If the sets differ, reject the trial.
Otherwise pass the bundle to the existing observer. A later streaming
probe can reject as soon as it produces a conflicting label.

```text
rawObservation = observe(rawPacket)
for candidate in existing_prefix_order:
    admission = probeRevisedAdmission(candidate, rawObservation.admission)
    if admission has a different label set: continue
    if admission is incomplete: observed = observe(candidate)
    else: observed = observe(candidate, admission.completeBundle)
    if observed == rawObservation: return candidate
return rawPacket
```

The admission label includes physical scope, family, raw start,
support and the possible binding used by the current equality test.
The probe emits no publication, permission, request or actual delivery.
Check every planned child as well as ordinary and qualified virtual
admission. Keep the current saved and enclosing checks for every
trial whose admissions agree. A proof of one conflicting label is
sufficient to reject; detecting a missing label requires the
complete iterator.

**Expected effect.** Remove saved replay and C5 from rejected prefix
trials. Reuse exact admission on trials that still need a full
observation. Check that the selected packet, raw fallback and outputs
are identical for plain, protected, typed and ND cases. Measure
reject-before-replay counts and the total number of complete
observations in Stirling-PDF run-3 and run-4. The profiles show the
cost of a full trial. Measure the number of trials that the probe
can reject before estimating the speedup.

## 5. Reuse raw entry and paired output work

**Current.** Revised C5 solves the raw C2 image for each candidate
pair. It can rerun the same witness search for one member and Dc across
many output rows. Accepted rows can then build the same bounded output
through independent selector and cut operations. The old prepared C5
plan uses a different, normalized entry predicate. The revised path
does not use that plan. In the Conductor run-2 CPU window, C5 appears in
11.51% of weighted samples and raw witness search in 7.64%.
[Raw witness and pair application](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/ap/RestrictedInitialPolicy.kt)

**Proposed.** Group candidates by the full Dc before checking the raw
membership. Reuse that answer over the Dp rows of that group. Within
the same offered packet, group the remaining work by the complete Dp
selector and its effective cap. Apply the selector once per group and
emit its output at every qualified pair and port that owns it. Use a
bounded prepared plan for repeated queries with the same frozen view.
Truncate reusable metadata at the normal query lifetime.

```text
for entryGroup in candidates.groupBy(complete_Dc):
    witnesses = rawMembers.filter(rawImage(entryGroup.Dc, member))
    if witnesses is empty: continue
    for outputGroup in entryGroup.groupBy(complete_Dp, effectiveCap):
        accepted = selectAndCut(rawResult, outputGroup.Dp, outputGroup.effectiveCap)
        for pairedRow in outputGroup:
            emit accepted at pairedRow with its qualified witnesses
```

Start with a query-local table before retaining a reusable plan.
Bind it to one offered packet and one physical demand view.
The check key includes the raw member, frozen policy and entry
selector, including any applicable mark or exclusion. The pair still
witnesses both endpoints. Projection still keeps every original ND
member and the correct output layer and protection. Qualification can
add a delta under a public row that already exists. A shared negative
entry result cannot reject a different raw shape. Test equality of
complete paired outputs and paired cut bounds with plans enabled and
disabled.

**Expected effect.** Remove repeated acceptance and cut work before
addressing allocation details. Track raw-image calls, paired operations,
selected outputs and callback counts. Add the revised-path counters
needed to distinguish rejected rows from output selections.

Restore the owner-quantum cache for loop C2 with the revised
complete binding as its value. The key includes the scope,
complete actual packet and frozen guard view. A result using
only the public initial omits the possible-binding service.
Conductor's `decide` made 1,061,221 native C2 calls with no reuse,
compared with 14,206 native calls and 13,764 cache hits before
the update. Use this change as a workload control because it
preserves the admitted family.

## 6. Coalesce identical local Target deliveries

**Current.** The local block pipeline matches a Target, completes the
whole ND join if needed and queues a callback to the parent. The
parent tests its exact raw Target set when the callback executes.
OWASP run-11 logged 433,878 local callbacks across the sampled loop
owners. `BenchmarkTest02326#doPost` accounts for 345,970. H11 retained
776 total rows after compaction of 25,694 projected obligations.
[Recipient callback](../../core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/engine/MethodBlockRuntime.kt)

**Proposed.** Count distinct recipient events first. For a parent
block entry, reserve the exact pair of complete original premise and
typed Target before queueing the first event. Subsequent matches
can share that pending or processed event. Use the recipient's
existing raw or processed set to avoid retaining a second copy
after delivery. Confirm the recipient uses the same admission
environment throughout the event lifetime.

```text
if recipient.alreadyProcessed(wholeOriginal, typedTarget): return
if recipient.reservePending(wholeOriginal, typedTarget):
    queue the existing terminal delivery
```

Keep the identity of the NormalTarget report, the recipient scope
and the complete original. Finish each match and the full ND join
before coalescing. Coalescing covers exact duplicates. The output
of a pending event has the same effect as its identical repeat
when the input selectors and recipient are fixed.

**Expected effect.** Reduce callbacks and allocation without
changing the frontier or report. Measure distinct recipient keys
against attempts before implementation. If initial churn is large,
test exact early projection during handoff separately. Use the
complete paired row, owner, physical ports and applicable literal
protection in any exact compaction proof.

For accepted Target production, share the terminal qualification
search with the acceptance test. Index explicit pairs with a ZERO
exit under the same physical view and entry selector. A query can
visit these pairs once and return both the acceptance bit and the
complete qualification set. Keep the existing virtual and borrowed
control views as separate inputs. When qualifications are required,
the first matching pair proves acceptance and the search continues
for the other eligible bindings. Validate the indexed candidate set
against the full control-pair scan. This addresses the additional
hot path seen in 61 of the 100 phase-aligned OWASP run-11 Java
execution samples.

## Cutoff decisions

Require a trace from the original offer through C2 or saved replay,
paired C5, and the retained handoff before changing a refinement
rule. A repeated post-handoff key can have multiple producers.
A rule bug requires an observed enabled guard and a different
native result. A pending LOOP or REC rule requires its specific
termination witness. An uncovered case needs a small cold-start
fixture with the same renewal and observation. Keep the
comparative activation gate in place while this work proceeds.

# Next iteration: proposals after the group A landing

Status: PROPOSAL, 25 November 2026. Input: the measurement of the group A
build `5804e44dd` ([report](../reports/bidirectional-group-a-landing-20261125.md)).
Design rules: [design-guide.md](../../spec/design-guide.md). Gate for every
item: confirmed and provisional results identical to the parent build, all
suites green, wall time and peak memory not worse. No item relaxes the FL+1
caps, and no item stops on reports.

## 0. Ranking

Rank = expected impact on the four measured projects. Algorithmic items
(remove work) come before technical items (do the same work cheaper) of
similar impact.

| # | Proposal | Kind | Target | Evidence (report section) | Expected effect |
| ---: | --- | --- | --- | --- | --- |
| P1 | One geometry with an exact mark set in run-1 | algorithmic | ThingsBoard run-1 OOM (all 15 baseline findings missing) | §8: 14.7 marks per caller family, 17.4 per diagonal point row, 1.59 M concrete DemandTarget premises; 1.1 KB live heap per event | Removes the per-mark repetition of events and storage. The only item that changes the cost per event of ThingsBoard run-1 |
| P2 | Semi-naive, order-independent replay in loop blocks | algorithmic | Stirling-PDF stall in run 9/11 (2 of 3 launches), Conductor runs 4-8 | §7.2, §9: the same hand-off (±2 rows) gives 5 s or a timeout; `replaySaved` → `LoopOutputRestriction` 43-61% of the stalled windows | Makes the loop-block cost independent of the work order; removes repeated (offer × record) replays |
| P3 | Incremental canonicalization in `FlowGroup.addAll` | algorithmic | Conductor runs 4-8, Stirling runs 8/10, ThingsBoard summary stores | §7.1: Conductor run-7 tail 93% FLOW subsumption; in run 8, 94.5% of `addAll` is the two full passes, 1.6% the insert | Upper bound ~370 s of Conductor runs 4-8 and ~35 s of Stirling-PDF |
| P4 | Do not repeat prescan work in run-1 | algorithmic | run-1 of all projects | §6: alias analysis 8-38% and rule resolution 8-31% of run-1 samples | 5-20 s of run-1 per project |
| P5 | Keep the method forms across runs | algorithmic | runs >= 3 | §6: OWASP run-2 52% call-plan building; runs 3, 5-11 rebuild plans after the end-of-run cleanup (13-44%) | ~5-6 s per project in runs >= 3 |
| P6 | Joined-exit report location | fix | Stirling-PDF: 8 baseline findings shown at another `return` | §3.2 | The 8 location twins match the baseline |
| P7 | Smaller work units for a single-package project | technical | OWASP runs 1-2 | §6: 1-2 of 10 workers busy, 573 s of parked worker time in run-1 | Tens of seconds of OWASP's 100 s in runs 1-2 |
| P8 | No lock around a rule-cache miss | technical | run-1 and prescan of multi-unit projects | §6: workers blocked 198 s (ThingsBoard), 73 s (Stirling-PDF) in run-1; 137-414 s in prescans | Better run-1 parallelism |

Not proposed, with the reason:

- The OWASP period-2 repetition from run 7 (identical 214/269-row hand-offs)
  and the Conductor demand growth with K in the mutually recursive
  `ParametersUtils#replace/replaceList` (14.4 k → 128.6 k rows) are
  termination questions (requirement AC, the open K-saturation item of
  `natural-termination-proposal.md` §9), not performance items. A stop on
  the repetition would be a report-based or numeric stop.
- GC tuning: GC is off the critical path in the long tails; P2/P3 remove
  the allocation that drives it.
- An earlier ThingsBoard OOM verdict (forced full GCs, ~40 s): it saves
  time on a run that fails anyway. P1 is the fix.

## P1. One geometry with an exact mark set in run-1

**Current.** Run-1 uses FULL marks (`RunConfig.readRun1MarkMode`, default
since 23 October). A callee premise, a caller-input slot, a point
membership and a DemandTarget premise exist once per concrete mark:

```text
SubscriptionManager.joinRequests → forEachConcreteAnswer → InitialAnswersIn   // one premise per mark
CallerInputValues.add                                                          // one slot per (premise, call, group)
witness / emitArm → emitTarget → addTargets                                    // one DemandTarget per concrete premise
```

On ThingsBoard, 99.6% of caller mark pairs keep the same mark, a caller
family carries 14.7 marks and a diagonal point row 17.4 marks with the
same geometry. The live heap grows by ~1.1 KB per event; run-1 stops at
4.69 M of the 7.9-9.9 M events that it needs (older 16 GB runs).

**New.** A premise, slot, point row and DemandTarget carry one geometry
and an exact `MarkSet`. The analyzer splits the set only at a step that
selects marks: a cleaner with a selected mark, a mark check, the R1 mark
policy, a sink, a pass rule with a mark literal.

```text
premise  = (geometry, marks: MarkSet)          // was: one premise per mark in marks
apply(step, premise):
  if step.selectsMarks: for (part, ms) in step.split(premise.marks): emit(geometry', ms)
  else:                 emit(step(geometry), premise.marks)               // one event for all marks
```

**Why it improves.** The work and the storage become proportional to the
number of geometries, not geometries × marks. The results are the same by
construction when every mark-selective step splits exactly (each mark of
the set follows the same geometry through every non-selective step). The
GROUP mark mode is not this change: it merges the marks of one owner into
one atom and loses which mark is present.

**Gate and proof.** Lean: a mark-set premise is the union of the per-mark
premises for every step (a homomorphism lemma per step kind; the selective
steps split exactly). Native prototype behind a flag first (design-guide
rule 3), ThingsBoard run-1 event count and live heap per event, then the
four projects and the suites.

## P2. Semi-naive, order-independent replay in loop blocks

**Current.** When a value is offered to a loop block
(`MethodBlockRuntime.offerChild`), `replaySaved` replays every saved
record against it. Each replay applies a summary (`limitFacts`), then
observes and restricts the loop output
(`LoopConsumerObservation.observe`, `LoopOutputRestriction.restrictScalar`,
`LoopRestrictionSession.trial`), which queries the frozen demand
(`DemandStore.scanLocalInitials`, `RestrictedInitialPolicy.emitAdmissions`).
The query scratch lives one work quantum and holds at most 32 entries.
The amount of work depends on the order in which values and records
arrive: on Stirling-PDF almost the same hand-off into run 9 (1,086 or
1,088 rows; the difference is in `EmlProcessingUtils#decodeMimeHeader`)
gave 5.1 s in one launch, a timeout after 893 s in the next and 399 s in
the third (then a timeout in run 11). Native launches took 156 s and 371 s.

**New.** Replay each (offered value, saved record) pair once. Keep a
per-block, per-run set of replayed pairs; a new value replays all records,
a new record replays all values, nothing else replays.

```text
onOffer(v):  for r in records: if (v, r) !in done: done += (v, r); replay(v, r)
onRecord(r): for v in values:  if (v, r) !in done: done += (v, r); replay(v, r)
query(view, scalar): memo[run][view, policy, scalar] ?: scan(...)     // the demand trie is frozen for the run
```

**Why it improves.** Each pair is replayed once whatever the order, so
the loop-block cost no longer depends on scheduling. The memo removes the
repeated scans of a frozen trie. The result is the same set of facts if the
replay of a pair depends only on the pair and on the frozen demand of the
run. This is an assumption: if the restriction state of the block also
feeds the replay, the key must include that state. The counter run checks
it before the prototype.

**Gate.** First a counter run on the prototype branch: the number of
repeated (value, record) pairs in the stalled Stirling-PDF run and in
Conductor runs 4-8 (no counter was logged this time). Then the flag
prototype, three Stirling-PDF launches (the stall is order-dependent),
Conductor, the suites.

## P3. Incremental canonicalization in `FlowGroup.addAll`

**Current.** After every insert, also an insert that changes nothing,
`addAll` runs `compactPacket` and `subtractSubsumed(row, every other row)`
for all `k` rows, twice, plus a promotion scan: O(k²) trie subtractions
per insert. `compactPacket` walks each leaf path again from the root. In
Conductor run 8, 94.5% of the `addAll` time is in these passes and 1.6% in
the insert itself.

**New.**

```text
addAll(rows):
  changed = insert(rows)                      // the rows that the insert added or merged
  if changed.isEmpty(): return                // nothing to canonicalize
  for r in changed: subtractSubsumed(r, others); subtractSubsumed(others, r)   // only pairs with a changed row
```

**Why it improves.** If the canonical form is pairwise (each row minus the
rows that subsume it), an unchanged pair stays canonical, the work per
insert becomes O(changed × k), and an insert that changes nothing costs one
lookup. The promotion scan and the merges inside `insert` must be checked
against this assumption first; the property test below is the check.

**Gate.** Unit tests: the incremental result equals the full pass on
random groups (property test), both layers. Then Conductor and
Stirling-PDF.

## P4. Do not repeat prescan work in run-1

**Current.** The prescan runs intra-procedural alias analysis and
resolves rules. Run-1 runs alias analysis again (`JIRCallPlanBuilder.aliases`;
the same method logs its 10 s overrun in both phases) and resolves rules
again in a new resolver epoch for the bidirectional rule selection.

**New.** Keep the per-method alias result of the prescan and give it to
the call-plan builder. Keep the selection-independent part of rule
matching (name and signature match) across epochs, and apply the
bidirectional selection on the matched rules.

**Why it improves.** The work is the same function of the same input; it
is done once. Run-1 shares: alias 8-38%, rules 8-31%.

## P5. Keep the method forms across runs

**Current.** Each run ends with `MemoryManager.runWithMemoryManager`, whose
`finally` calls `cleanup()` on every soft-reference manager, the form
cache `bidi-method-forms` included. Runs >= 3 rebuild their call plans
(OWASP run 3 44%, Stirling-PDF runs 5-11 13-26% of samples).

**New.** Do not clean the form cache at the end of a run. Its entries
stay soft-reachable, so memory pressure still releases them.

**Why it improves.** A FULL call plan is the same in every run after run-1;
only the first FULL build (run 2) stays.

## P6. Joined-exit report location

**Current.** The bidirectional engine reports an exit sink at the joined
synthetic normal exit. Without a trace, `TraceMessageBuilder.tryResolveExitLocation`
(`TraceMessageBuilder.kt:1162-1167`) shows the last `return` of the
method. On Stirling-PDF, 8 baseline findings are shown at another `return`
of the same method and count as missing + extra.

**New.** Resolve the location to the `return` instructions whose value
carries the reported fact (one report per tainted `return`), as the legacy
engine does through its trace.

**Why it improves.** The reported location becomes the real one; the
comparison with the baseline loses 8 false "missing" rows. It changes
report rendering only, not the analysis.

## P7. Smaller work units for a single-package project

**Current.** `PackageUnitResolver` puts almost all OWASP methods in one
unit (`org.owasp.benchmark.testcode`). One `UnitRunner` processes a unit
sequentially, so runs 1-2 use 1-2 of 10 workers.

**New.** Split a unit above a size threshold into class-level units.

**Why it improves.** Runs 1-2 (100 s) can use the idle workers. The order
of work changes, so the result gate applies.

## P8. No lock around a rule-cache miss

**Current.** `TaintConfiguration.ResolverView.cached` resolves a miss inside
`synchronized(cache)` (one cache per rule kind), and
`TaintRulesStorage.resolveItems` is `@Synchronized`.

**New.** A per-key future (`ConcurrentHashMap.computeIfAbsent` per key),
no storage-wide lock.

**Why it improves.** Workers stop waiting for each other on unrelated keys.

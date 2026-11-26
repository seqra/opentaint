# Next iteration: proposals after the P3 landing

Status: PROPOSAL, 26 November 2026. Input: the landing measurement of P3
and P2' ([report](../reports/bidirectional-p3-p2m-landing-20261125.md)).
P3 is landed (`0919c7500`). P2' was measured and reverted (`c89881544`):
it kept all results and made the Conductor loop runs faster, but it
added 0.8-1.4 GB to the heap after GC of the long loop runs and failed
the memory gate. N4 below proposes it again with a bounded footprint.

Design rules: [design-guide.md](../../spec/design-guide.md). The gate for
every item:

- confirmed and provisional results identical to the parent build;
- all suites green (module, jvm, rule suite in bidirectional mode, Lean);
- wall time, heap after GC (the launch maximum and each run) and GC pause
  time not worse beyond the spread of the parent launches.

No item relaxes the FL+1 caps. No item stops on reports, cuts work by a
number, or switches a rule off in a scope. A census runs only on a proto
branch; the landed code has no switch, no census and no counter.

Data paths in this document are relative to the campaign directory
`/drive-testcomp/opentaint-go-rules/p3p2m-landing-20261125/`. Code paths
are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

## 0. Ranking

Rank = expected effect on the four measured projects. A false negative
(ThingsBoard) ranks before a timeout, and a timeout before a slow
complete run. Algorithmic items (remove work or stored state) come before
technical items (do the same work at a lower cost) of similar effect.

| # | Proposal | Kind | Target | Evidence | Expected effect |
| ---: | --- | --- | --- | --- | --- |
| N1 | Release the working state of complete subgoals in run 1 | algorithmic | ThingsBoard run-1 OOM: all 15 baseline findings missing | Report §9: the barrier does not read 2.2 GB of the 6.29 GB engine state; memory per stored membership is constant, so the heap follows all past work | Up to 3.4 GB at the guard. The heap grows with open work, not with all work |
| N2 | Incremental TAINT canonicalization (P3 for `TaintGroup`) | algorithmic | Stirling-PDF stall (3 of 3 landed launches time out); Conductor runs 6 and 8 | Report §8.3: `TaintGroup.addAll` 21-52% of the analyzer samples of each Stirling stall (64-83% of the Java samples with the restriction memoized) | A stalled offer costs 1.3-2.1 times less; 1.6-4.4 times with N4 (upper bounds) |
| N3 | One normal form for stored FLOW and TAINT rows | algorithmic | The trigger of the Stirling-PDF stall; repeatable launches on all projects | Report §10.1: 18 of 18 launches: the fast hand-off split completes, every other split times out | If the normal form is the fast split: no Stirling stall. Every gate becomes repeatable |
| N4 | Restriction memo with a bounded footprint (P2' again) | algorithmic | Conductor runs 4, 6 and 8 | Report §6: against P3 alone, P2' made run 4 -49% and runs 1-7 -14.5%, but added 0.8-1.4 GB to the heap after GC of the loop runs | The P2' time gain inside the memory gate |
| N5 | One store set per loop method, not per loop block | algorithmic | ThingsBoard run-1 heap | Report §9: 1,276 loop actors (1.8% of actors) hold 1.59 GB (45% of actor bytes) | About 1.0-1.3 GB at the guard |
| N6 | Compact engine representations | technical | ThingsBoard run-1 heap | Report §9: collection structures are 63% of engine bytes; most sets hold 1-2 elements | About 2.1-2.4 GB at the guard |
| N7 | Recompact only the changed rows | algorithmic | Conductor run 7 | Report §8.2: run-7 tail 82% `FlowGroup.addAll`; 74% of it from `FlowBackedSummaries.recompact` | Most of the 61 s of run 7 |
| N8 | Run-level admission answers for loop trials | algorithmic | Conductor run 8 | Report §10.2: trials 44-47% and the demand-view scan 28-31% of analyzer samples | Fewer repeated scans; size not known before the census |
| N9 | A Work priority that counts block work | technical | Single-thread tails (Conductor, Stirling-PDF) | Report §10.1: 11-12 events stay in flight for minutes while one owner works | Callees finish before the owner works on old summaries |
| P4-P8 | Carried over from the previous proposal | | run 1, runs ≥ 3, OWASP, report locations | Report §7, §8.4 | As in the previous proposal |

Order of work: N2 and the censuses of N1, N3 and N4 first (they are
independent and the censuses decide the design of N1, N3 and N4). Then N3
before N9, because N9 changes the work order and is exact only when the
fixpoint does not depend on the order.

## N1. Release the working state of complete subgoals in run 1

**Current.** Run 1 keeps the working state of every actor until the
run-1 barrier. At the ThingsBoard guard (4.33 M events, 11.39 GB
reachable), the engine holds 6.29 GB: actors 3.55 GB, caller inputs
1.83 GB, callee storages 0.84 GB. The engine bytes per stored membership
are constant over the run (374 B; parent 368 B), so the heap follows all
the work done so far, not the open work. The barrier reads only the
actor exports, and the caller and local inputs of the static-writer
binding (568 writer rows). It drops the other state without reading it:
`freeze` drops the point edges (0.98 GB), the point resumes (0.23 GB) and
the local services (0.24 GB); `detachJoinedSubscribers` drops the
publication indexes (0.76 GB).

**New.** A subgoal is an actor (or a block scope) with one premise. It is
complete when its worklist is empty and every subgoal that it waits on is
complete. One strongly connected group completes together, as in tabled
resolution. When a subgoal completes:

```text
onComplete(subgoal):
  drop pointEdges(subgoal), pointResumes(subgoal), localEvidence(subgoal)
  keep summaries(subgoal), publications(subgoal)        // the barrier reads them
  for callerPremise in callerInputs(subgoal.actor):
    if all matched callee subgoals of callerPremise are complete
       and callerPremise is not on a static-writer chain:
      drop callerInputSlots(callerPremise)
```

**Why it improves.** The dropped state is the state that the barrier
does not read. Today it stays until the barrier, so the heap at the guard
holds the working state of all finished work. With the change, it holds
the working state of open work only. The upper bound at the ThingsBoard
guard is 3.4 GB (working state 1.6 GB, caller inputs 1.83 GB, less the
static chains). Earlier 16 GB launches needed 7.9-9.9 M events to finish
run 1, and N6 alone moves the guard to only 6.5-7.0 M events. So N1 (with
N5) is the only item that can let run 1 finish.

**Exactness.** A complete subgoal must get no new delta in the run. An
in-run static effect (`onStaticEffect`) can add a dependency after
completion; the completion rule must include it. This needs a Lean proof:
completion is stable, and the barrier output is the same with and without
the drop.

**Census first (proto branch).** At the guard: the number of complete
subgoals and the bytes that their working state holds. The saving above
is an upper bound until this census exists.

## N2. Incremental TAINT canonicalization

**Current.** `TaintGroup.addAll` (`ap/Groups.kt:235-255`) copies the
lane, merges the packet into the row with the same header, and calls
`canonicalize` (`:285-310`) on the whole lane. `canonicalize` repeats
three steps until a pass changes nothing: the merge closures
(`mergeEqualHeaders`, `mergeSpanExclusions`, `fillMustHole`), an ANY
self-subtraction of each ANY and ANY_TAINT row, and `subtractSubsumed` of
each row against all other rows. So each insert that changes a row costs
at least two full passes. After it, `minusNode` runs for each kept row
against its old row. Each `subtract` call builds a new memo `HashMap`
(`ap/TrieOps.kt:457`). The cost of one insert follows the size of the
lane, not the size of the change.

**New.** The P3 rule for TAINT lanes:

```text
addAll(packet):
  before = lane.toList()
  mergeHeader(lane, packet)
  if sameRows(lane, before): return []                  // no row object changed
  canonicalize(lane, clean = before)                    // a clean row is subtracted only by dirty rows
  return [newPart(row, before) for row in lane if row is dirty]
canonicalize(lane, clean):
  loop:
    dirty = rows of lane not in clean (by identity)
    for row in lane:
      if row in clean: row = subtractSubsumed(row, dirty)
      else:            row = subtractSubsumed(anySelfSubtract(row), lane - row)
    clean = lane
    if a merge closure changed the lane: continue       // the merged rows are dirty
    break
on a throw: restore before
```

**Why it improves.** Invariant F holds for the clean rows: they are
already canonical against each other, so a pass that subtracts them from
each other changes nothing. The work per insert becomes proportional to
(dirty rows × lane size), and an insert that changes nothing costs one
merge. Measured shares (report §8.3, §10.1): in the Stirling stall
windows of the landed build, `TaintGroup.addAll` is 20.8-52.4% of the
analyzer samples, second to the restriction (41.8-74.8%). With the
restriction memoized (P3 + P2'), it was 63.8-83.0% of the Java samples,
`TaintGroup.canonicalize` 38.8-77.2% of the analyzer samples, and the top
self frame `SubtractKey.equals` (18.2-34.7%). In Conductor run 6 it is
17.3% of the analyzer samples. P3 did the same for FLOW and cut
`FlowGroup.addAll` in Conductor run 8 from 22.0% to 7.9% of the analyzer
samples. If the TAINT share goes to zero, a stalled offer costs 1.3-2.1
times less, and 1.6-4.4 times less together with N4. N2 does not change
the number of offers, so it does not remove the stall alone.

**Exactness.** The same proof shape as P3 (`FlowGroupIncremental.lean`,
`FlowGroupIncrementalImpl.lean`). The three merge closures must be in the
model, as the P3 model has the MUST merge and the promotion. The test is
the P3 test: a copy of the native `TaintGroup` as a reference, random
insertion sequences, equal deltas and rows after each call, invariant F
after each call.

## N3. One normal form for stored FLOW and TAINT rows

**Current.** The split of the stored facts into rows depends on the
arrival order:

- a new FLOW row loses the coordinates that a stored row covers
  (`ap/Groups.kt:20-57`);
- the MUST merge, the promotion, `mergeSpanExclusions` and `fillMustHole`
  act on the first match in list order;
- `TaintGroup.canonicalize` subtracts in reverse list order.

The hand-off projects these rows (`driver/HandOff.kt:49-72`). So two
launches with the same input can hand off a different number of rows.

**Evidence.** On Stirling-PDF the stall owner is
`EmlProcessingUtils#decodeMimeHeader(String) [{}]`. In 18 launches of
this core, the owner gets 234 or 238 rows at frontier 6 in each of the 5
fast launches (all complete; runs 9 and 11 take 1.6-5.8 s). It gets 1 or
3 rows more in each of the 13 slow launches (all time out). With P3
active, 1 of 9 launches was fast; without it, 4 of 9. This is not
significant (Fisher exact test, one-sided p = 0.15), but it shows that
the timing of the work can move the split, so the landed Stirling-PDF
gate (3 launches) cannot see the effect of a change on the stall. The split
starts in run 5 (1.0-1.7 s), whose input has equal per-key counts in all
launches: its output on the owner is 181 or 166 rows, and the owner gets
2,467 or 1,006 offers. Other counts also change from launch to launch of
one build: the OWASP hand-off rows after run 5 (62, 91, 160 or 189) and the Stirling run-3 raw targets (654 or 681). The results
do not change.

**New.**

1. Census (proto branch; items 1-3 of `analysis/stall.md` §4). For the owner at the run-6
   barrier, in one fast and one slow launch: each stored row, and one
   digest of the union per (premise, base, layer). Equal union and
   different rows prove that the order changes only the split (H1). A
   different union means that an operator is not confluent; the insert
   log of runs 4-6 then finds it.
2. If H1 holds: make the stored rows a function of the set of facts. Give
   each covered coordinate to the most general covering header; break
   ties by a fixed total order on headers (tail, exclusion, mark
   exclusion). Run the merge and promotion closures to their fixpoint in
   that fixed order. Prove in Lean that the rows depend only on the union
   and serve the same facts as today.
3. A smaller first step: apply the normal form only to the demand rows in
   `HandOff.toCompacted`, before `compactor.select`.

**Why it improves.** The same facts give the same hand-off and the same
next run in every launch. If the normal form gives the fast split, the
Stirling stall goes away (each of the 5 fast launches completed; two of
them took 92 s and 160 s of engine time). It also removes the rework where a specific row arrives
before the general one, because one coordinate has one owner whatever
the order. And it makes each later gate repeatable: today one launch per
project cannot show a change below the order noise.

**Risk.** The normal form can be the slow split. Then Stirling-PDF stalls
in every launch. The census must show which split the normal form gives
before the change lands (234 or 238 rows on the owner at frontier 6).

## N4. Restriction memo with a bounded footprint

**Current (after the revert).** `onApplied` computes the loop-output
restriction (`LoopOutputRestriction.restrict`) for each applied
completion. Inside one run, 73-90% of the calls repeat a key (Conductor
census of the earlier proto branch). The P2' memo kept up to 1,000,000
entries per method runtime and cleared all of them when full. Measured
against P3 alone (report §6), with all results equal: Conductor run 4
-49%, run 6 -10%, runs 1-7 -14.5% (84 s). But:

- the heap after young GC grew by 0.8-1.4 GB in Conductor runs 6-8 and
  by 1.1-1.4 GB in the Stirling-PDF stall runs; about 0.9 KB of live heap
  per entry. The launch maximum did not change, because the prescan and
  runs 1-3 set it;
- Conductor GC pauses went from 20.3-20.5 s (parent, P3 alone) to 34.5 s;
- Conductor run 2 was 9.5% slower. The prototype, with a plain
  `SoftReference` and all calls kept, was not; the cause is not found;
- the memo lookups walked tree bins (400,678 `HashMap$TreeNode` objects in
  Conductor run 8). The trie hash is a sum over children, and each level
  shifts the child hash by 5 bits (`ap/Trie.kt:60`); `hashCode` keeps the
  low 32 bits (`:76`). So nodes that differ only at depth 7 or more have
  the same `hashCode`;
- with a cap of 1 M entries, the prototype hit 39.5% of the calls in
  Conductor run 8 with 7 full clears, against 73.4% possible.

**New.**

1. A budget in trie nodes, not in entries. The memo adds the `size` of
   the key value and of the result values. It keeps two generations of
   at most B/2 nodes each. When the young generation is full, it drops
   the old one, and the young one becomes old. A hit in the old
   generation moves the entry to the young one.
2. A 64-bit digest of the value, with full mixing at each level, computed
   once per interned node and used only by the memo key. `equals` runs
   only when the digests are equal. `TrieNode.hashCode` does not change:
   `HashMap` iteration orders depend on it, and the order changes the
   hand-off split (N3).
3. The memo stays soft through `ap.softRefs` and is cleared in
   `freezeChildren`, as in P2'.

B comes from a census on a proto branch: the reuse distance of the keys
and the nodes per entry, in Conductor runs 4-8 and in a Stirling stall.
B must keep the heap after GC of each loop run, and the GC pause time,
inside the spread of the parent launches.

**Why it improves.** The restriction is a function of the key inside one
run (P2' proof, `RestrictionMemo.lean`), so a hit removes the work. The
budget limits the heap; the generations keep the entries that recur; the
digest removes the tree-bin walks. Upper bound for Conductor run 8: 2.3
times fewer restriction computations.

**Exactness.** Unchanged from P2': the memo changes no answer. The
generations and the digest change only which keys hit.

## N5. One store set per loop method, not per loop block

**Current.** Each loop block of a method runtime has its own full set of
stores. At the ThingsBoard guard, 1,276 loop actors (1.8% of the actors)
hold 1.59 GB (45% of the actor bytes) in 11,602 block entries: local
inputs 0.45 GB, child block states 0.59 GB, link publications and
targets 0.31 GB, completions 0.10 GB.

**New.** One store set per loop method, with the block scope as part of
the row key; or derive the block exports at the barrier from the method
store.

**Why it improves.** About 1.0-1.3 GB at the guard. The run-2 hand-off
needs the scoped exports, so this item needs a design that keeps them.

## N6. Compact engine representations

**Current and new** (report §9; each change is exact):

| Change | Current | Saving at the guard |
| --- | --- | ---: |
| Caller families: the cells of a source as an int array; `changingByTarget` on the first non-diagonal pair | 2.61 M sets with 1.38 cells each; 527,954 maps for 45,335 entries (`CallerMarkRelations.kt:8,63,71`) | 0.7 GB |
| One Target value per premise in `PublicationIndex.targets` | 1.74 M one-element sets (`PublicationIndex.kt:16,72`) | 0.4 GB |
| Replacement indexes on first use | 964,214 sets for 367,550 elements; point stores never use them (`FlowBackedSummaries.kt:16-17`) | 0.28 GB |
| Interned small keys (`GroupKey` at `Facts.groupKey`) | 4.27 M `GroupKey` objects, 2,856 values | 0.4 GB |
| One hash-cons table for tries, headers and mark sets | 1.33 M trie nodes for 33,827 subtrees; 1.76 M headers for 37,112 values | 0.3-0.4 GB |
| `PathTrie` posting sets as int arrays | 1.13 M `LinkedHashSet` objects (`PathTrie.kt:11`) | part of 0.47 GB |

**Why it improves.** Together about 2.1-2.4 GB of 6.29 GB engine state.
This moves the ThingsBoard guard to about 6.5-7.0 M events. It is not
enough alone (N1).

## N7. Recompact only the changed rows

**Current.** `FlowBackedSummaries.recompact` (`store/FlowBackedSummaries.kt:42-76`)
builds a new `ConclusionGroup` for each affected premise and adds every
current row to it again, after `removeAlignedFlowCovered`. Each added row
is new to the empty group, so P3 treats it as dirty, and `compactPacket`
walks all its leaves from the root. In the Conductor run-7 tail,
`FlowGroup.addAll` is 82% of the Java samples, 74% of these calls come
from `recompact`, and 91% of their time is `compactPacket`.

**New.** Start from the current rows. Keep the row objects that
`removeAlignedFlowCovered` does not change as clean, and replace only the
changed rows. Then run the P3 `canonicalize(list, clean)`.

**Why it improves.** The current list satisfies invariant F, so the
unchanged rows need no `compactPacket` and no subtraction among
themselves. The work follows the number of changed rows.

**Exactness.** P3 proves that `canonicalize` with a clean set gives the
full-pass result when the clean rows are a fixpoint. Removing rows from a
fixpoint list keeps the clean pairs canonical, but it can enable a
promotion; `canonicalize` already checks the promotion on the whole list.
The Lean model must state this precondition; the test compares with
today's `recompact`.

## N8. Run-level admission answers for loop trials

**Current.** A restriction computation runs trials. Each trial probes
the admissions with `probeLoopAdmissions` (`engine/LoopQueryScratch.kt:112-152`):
it scans the frozen demand view and calls `RestrictedInitialPolicy.fitsBudget`
and `emit` for each emission. `LoopQueryScratch` keeps answers for one
work quantum only, at most 32 of them, and none with more than 128 rows.
In Conductor run 8, trials are 43.8-47.1% and `scanLocalInitials`
28.2-31.0% of the analyzer samples. The owners `ParametersUtils#replace`
and `replaceList` hold 57,740-70,839 demand rows, so most answers are
larger than 128 rows and are never kept.

**New.** Keep the admission answers for the whole run, keyed by (view,
policy, packet), with the N4 budget and generations. Then index the view
by the packet head (base and first accessor), so that a scan visits only
rows that can match.

**Why it improves.** The view is frozen for the run, so an answer is a
function of the key (the P2' argument). The hit rate is not known: the
existing `-Dorg.opentaint.bidi.optimizationStatistics=true` statistics
(`c2Queries`, `c2Hits`) on a proto launch measure it first.

## N9. A Work priority that counts block work

**Current.** `EventQueue` orders Work events by `steps`
(`engine/EventQueue.kt:12-16`). `steps` counts statement edges only
(`BlockRunState.kt:572`), not offers, replays or completions in
`MethodBlockRuntime`. So a loop owner keeps a low key during its local
fixpoint, and other Work of the same package runner waits. In the
Conductor and Stirling tails one thread works (91-99% of the 5-second
buckets) while 11-12 events stay in flight.

**New.** Add the block-runtime work units (`workQuantum`,
`MethodBlockRuntime.kt:176-195`) to the priority key, or serve waiting
Work events in turn after each quantum.

**Why it improves.** If the waiting events include callees of the owner,
the owner works on old callee summaries and must do the general work
again later. This is a hypothesis from the code (H2 of `analysis/stall.md`):
census item 6 (the runner queue at each progress tick) must confirm it first.

**Exactness.** N9 changes only the order. The final facts stay the same
only if the fixpoint does not depend on the order, so N9 comes after N3.

## P4-P8. Carried over

The evidence of the previous proposal
([bidirectional-next-iteration-20261125.md](bidirectional-next-iteration-20261125.md))
did not change:

| # | Proposal | Evidence in this measurement |
| --- | --- | --- |
| P4 | Do not repeat prescan work in run 1 | Run-1 shares: alias analysis 8.6-39.0%, rule resolution 7.9-31.3% (report §7) |
| P5 | Keep the method forms across runs | OWASP `FormsCache.payload` 56.8% of run-2 and 47.0% of run-3 Java samples (report §8.4) |
| P6 | Joined-exit report location | The 8 Stirling-PDF location twins remain (report §3) |
| P7 | Smaller work units for a single-package project | OWASP run-1 profile window: about one analyzer core of 20 (report §11) |
| P8 | No lock around a rule-cache miss | Rule-cache waits: ThingsBoard prescan 536 s and run 1 231 s; Conductor prescan 166 s (report §8.4) |

## Not proposed

- **A change of `TrieNode.hashCode`.** It is weak (N4), but `HashMap`
  iteration orders depend on it, and the order changes the hand-off split
  (N3). After N3 lands, a better hash is a plain technical item.
- **The P1 cohort form** (one geometry with a mark set across the call
  boundary). It was withdrawn after its ablation: 90% of the answers
  dropped and the memory per event did not change.
- **A stop on repeated hand-offs** (OWASP period 2 from run 7) or on the
  Conductor demand growth with K. These are termination questions; a
  stop on them would be a report-based or numeric stop.
- **GC tuning.** The extra GC time came from the P2' memo, which is
  reverted. N4 bounds the memo instead.
- **Replay of saved records on the link delta only** (`analysis/stall.md`, C6).
  Only 0.02-0.04% (Stirling-PDF) and 0.7-2.7% (Conductor) of the offered
  leaves were offered before on the same link.

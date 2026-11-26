# Next iteration: proposals after the backward condition progress landing

Status: PROPOSAL, 26 November 2026. Input: the landing measurement of R1
and R2 ([report](../reports/bidirectional-backcond-landing-20261126.md)).
R1 (`4af723e80`) and R2 (`ba69bbb72`) are landed. They changed no result
and no measured cost (report §3, §4.2, §6). So the problems of the
parent proposal
([bidirectional-next-iteration-20261126.md](bidirectional-next-iteration-20261126.md))
stay, with the same evidence or new evidence. This document ranks them
again and adds the items that this landing found.

Design rules: [design-guide.md](../../spec/design-guide.md). The gate for
every item:

- confirmed and provisional results identical to the parent build;
- all suites green (module, jvm, rule suite in bidirectional mode, Lean);
- wall time, heap after GC (the launch maximum and each run) and GC pause
  time not worse beyond the spread of the parent launches;
- **new:** on a shared machine, the time gate compares the two builds in
  interleaved launches on the same machine state (report §4.2). Single
  launches at a different load are not comparable: in this landing the
  same code ran 13-18% slower at a load of 12 than at a load of 3-5.

No item relaxes the FL+1 caps. No item stops on reports, cuts work by a
number, or switches a rule off in a scope. A census runs only on a proto
branch; the landed code has no switch, no census and no counter.

Data paths are relative to the campaign directory
`/drive-testcomp/opentaint-go-rules/backcond-landing-20261126/`. Code
paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.

## 0. Ranking

Rank = expected effect on the four measured projects. A false negative
(ThingsBoard) ranks before a timeout, and a timeout before a slow
complete run. Algorithmic items (remove work or stored state) come before
technical items (do the same work at a lower cost) of similar effect.

| Rank | # | Proposal | Kind | Target | Evidence (this landing) | Expected effect |
| ---: | ---: | --- | --- | --- | --- | --- |
| 1 | N1 | Release the working state of complete subgoals in run 1 | algorithmic | ThingsBoard run-1 OOM: all 15 baseline findings missing | Same wall at 4.33 M events (parent 4.34 M); working state of finished work 1.70 GB and caller inputs 1.80 GB at the guard (report §9) | Up to 3.5 GB of 6.27 GB engine state at the guard; the heap follows open work, not all work |
| 2 | N3 | One normal form for stored FLOW and TAINT rows | algorithmic | The trigger of the Stirling-PDF stall | Report §10: signature in 21 of 21 launches; the new launches repeat parent row paths key by key | No stall if the normal form gives the fast split; repeatable gates |
| 3 | N2 | Incremental TAINT canonicalization | algorithmic | Stirling-PDF stall; Conductor runs 6 and 8 | `TaintGroup.addAll` 21-41% of the stall samples (report §10) | A stalled offer costs 1.3-2.1 times less (upper bound, parent census) |
| 4 | N4 | Restriction memo with a bounded footprint | algorithmic | Conductor runs 4, 6, 8; Stirling-PDF stall | `replaySaved` 85-99%, `restrict` 61-85% of the long backward runs, unchanged (report §8) | The P2' gain (Conductor run 4 -49%) inside the memory gate |
| 5 | N5 | One store set per loop method | algorithmic | ThingsBoard run-1 heap | Loop runtimes 1.59 GB: 1.8% of the actors hold 43.5% of the actor bytes (report §9) | About 1.0-1.3 GB at the guard |
| 6 | P5 | Keep the method forms across runs (census of rebuilds first) | algorithmic | OWASP (CI) runs 1-2; ThingsBoard run-1 time | Form building 49% of OWASP run 1, 57% of run 2, 44% of ThingsBoard run 1 (report §8) | Up to half of OWASP runs 1-2 if most builds are rebuilds; not known before the census |
| 7 | N7 | Recompact only the changed rows | algorithmic | Conductor run 7 | `recompact` 47%, `FlowGroup.addAll` 58% of run 7 (report §8) | Most of the 61-75 s of run 7 |
| 8 | N8 | Run-level admission answers for loop trials | algorithmic | Conductor runs 4, 6, 8 | `trial` 30-48%; `RestrictedInitialPolicy.fitsBudget` is the top own-time frame of every backward run (5-6%) | Fewer repeated scans; size not known before the census |
| 9 | N6 | Compact engine representations | technical | ThingsBoard run-1 heap | Engine-owned collection structures 3.94 GB, 62.9% of the engine state (report §9) | About 2.1-2.4 GB at the guard; not enough alone |
| 10 | N9 | A Work priority that counts block work | technical | Single-thread tails | Stirling-PDF run 9: one thread for 820-850 s with 11-12 events in flight (report §10) | Callees finish before the owner works on old summaries (hypothesis) |
| 11 | N10 | An annotation index for rule resolution | technical | ThingsBoard run-1 time | `TaintRulesStorage.configForMethod` 24% of run 1, linear scan with `AnnotationConstraint.equals` | Up to 24% of ThingsBoard run 1; no effect on the OOM |

Design follow-ups of R1 and R2 (no performance target; they decide the
next step of the convergence work):

| # | Item | Evidence | Outcome |
| ---: | --- | --- | --- |
| B1 | Why R2 gives no progress: the PG anchor and `AuthController#login` | Report §6.2: on PG, R1 alone confirms the finding in the same runs as R1 + R2; on Stirling-PDF the run frontiers are the same as without R2 in each run, and `login` stays in each | The cut that keeps `login` in demand; then a test that needs R2, or a corrected §I.2/§II.1/§II.5 and a decision on R2 |
| B2 | The cause of the 2 provisional Stirling-PDF findings | Report §3.2: `xss#sink#1` in `UserController` stays provisional with R2 | The rule, literal and cut that keep them provisional |

Order of work: the censuses of N1, N3, N4 and P5 first (they decide the
designs and are independent). B1 also starts first: it decides the next
step toward the main acceptance criterion (acyclic code converges), and
R2 did not move its case. N2 can start at once. N3 before
N9, because N9 changes the work order and is exact only when the
fixpoint does not depend on the order.

## N1. Release the working state of complete subgoals in run 1

**Current.** Run 1 keeps the working state of every actor until the
run-1 barrier. The barrier reads only the actor exports, and the caller
and local inputs of the static-writer binding. It drops the rest without
reading it. This landing hits the same wall: OOM at 4.33 M events
(parent 4.34 M). At the guard the engine holds 6.27 GB of the 11.37 GB
heap. The working state that the barrier drops unread is 1.70 GB (point
edges 0.99, point resumes 0.24, local services 0.25, worklists and queues
0.23); the caller inputs are 1.80 GB; the publication indexes 0.73 GB
(report §9). The exports that the barrier reads are 0.58 GB. R2 adds one
export (the capture trees, 8.9 MB): N1 must keep it with the summaries.

**New.** As in the parent proposal: when a subgoal (actor or block scope
with one premise) completes, drop its point edges, point resumes and
local evidence; keep its summaries and publications; drop the
caller-input slots of a complete caller premise whose matched callee
subgoals are complete, except on static-writer chains.

**Why it improves.** The dropped state is the state that the barrier does
not read. The heap at the guard then holds the working state of open work
only. N1 (with N5) is the only item that can let ThingsBoard run 1
finish: earlier 16 GB launches needed 7.9-9.9 M events.

**Census first.** The number of complete subgoals at the guard and the
bytes of their working state. The saving is an upper bound until then.

## N3. One normal form for stored FLOW and TAINT rows

**Current.** The split of the stored facts into rows depends on the
arrival order. In Stirling-PDF, the stall owner
`EmlProcessingUtils#decodeMimeHeader` gets 1-3 extra hand-off rows after
run 6 in each slow launch and none in each fast launch. This landing
adds 3 launches (+3, +3, 0): 21 of 21. Only 6 distinct row paths occur,
and the new launches copy parent paths key by key.

**New.** A normal form of the stored rows that does not depend on the
arrival order (parent proposal N3), after the census of the owner rows
at the run-6 barrier in one fast and one slow launch (runs 1-7 only).

**Why it improves.** The same facts give the same hand-off in every
launch. If the normal form is the fast split, the stall goes away, and
every gate becomes repeatable.

## N2. Incremental TAINT canonicalization

**Current.** `TaintGroup.addAll` copies the lane, merges the packet and
canonicalizes the whole lane on each insert. It takes 21-41% of the
analyzer samples in the Stirling-PDF stall windows of this landing.

**New.** The P3 rule for TAINT lanes: keep the clean rows canonical
against each other and canonicalize only the dirty rows against the
lane.

**Why it improves.** The work per insert follows the dirty rows, not
the lane. An insert that changes nothing costs one subsumption check.

## N4. Restriction memo with a bounded footprint

**Current.** `LoopOutputRestriction.restrict` runs again for each applied
completion. In this landing it takes 61-85% of the Conductor backward
runs and 54-74% of the Stirling-PDF stall, unchanged. Inside one run
73-90% of the calls repeat a key (parent census).

**New.** The P2' memo with a budget in trie nodes, two generations and a
key digest (parent proposal N4).

**Why it improves.** The restriction is a function of the key inside one
run, so a hit removes the work; the budget keeps the heap inside the
gate that P2' failed (+0.8-1.4 GB).

## N5. One store set per loop method, not per loop block

**Current.** Each loop block has its own full store set. At the
ThingsBoard guard, 1,276 loop actors (1.8% of the actors) hold 1.59 GB
(43.5% of the actor bytes): local inputs 0.44 GB, child block states
0.60 GB, link publications and targets 0.30 GB, completions 0.10 GB. R2
already shares one capture store per loop method (the child block states
reference the root store).

**New.** One store set per loop method with the block scope in the row
key, or block exports derived at the barrier.

**Why it improves.** Removes the per-block copies (about 1.0-1.3 GB at
the guard).

## P5. Keep the method forms across runs

**Current.** `FormsCache` keeps each form behind a soft reference in the
per-method interpreter entry (`interp/FormsCache.kt`). Run 2 builds the
reversed forms. The MemoryManager clears soft references near its
threshold ("Cleaned soft refs" in ThingsBoard), so forms can be built
again. Form building (`FormsCache.payload` → `JIRCallPlanBuilder.build`)
takes 49% of OWASP run 1, 57% of OWASP run 2 and 44% of ThingsBoard
run 1 (report §8).

**New.**

1. Census first: `FormCacheStatistics` already counts builds, hits and
   reversals. Run it on a proto launch of OWASP and ThingsBoard and
   split the builds into first builds and rebuilds after a clear.
2. If rebuilds are a large share: keep the forms of methods with open
   work strongly reachable, and clear only the forms of methods with no
   open work; or keep the call plan, which does not depend on the rule
   view, apart from the rule payload.

**Why it improves.** A rebuild repeats work that the run already did.
OWASP is the CI project; runs 1-2 are 82% of its engine time.

## N7. Recompact only the changed rows

**Current.** `FlowBackedSummaries.recompact` builds a new group for each
affected premise and adds every current row again. In this landing:
47% of Conductor run 7 (`FlowGroup.addAll` 58%).

**New.** Keep the rows that `removeAlignedFlowCovered` does not change as
clean, replace only the changed rows, then run the P3 canonicalization.

**Why it improves.** The work follows the changed rows, not all rows.

## N8. Run-level admission answers for loop trials

**Current.** Each trial scans the frozen demand view and calls
`RestrictedInitialPolicy.fitsBudget` and `emit` per emission. In this
landing `trial` takes 30-48% of the Conductor backward runs, and
`fitsBudget` is the top own-time frame in every backward run (5-6%).

**New.** Keep the admission answers for the whole run, keyed by (view,
policy, packet), with the N4 budget; index the view by the packet head.

**Why it improves.** The view is frozen for the run, so an answer is a
function of the key. The hit rate comes first from the existing
optimization statistics on a proto launch.

## N6. Compact engine representations

**Current.** Engine-owned collection structures are 3.94 GB, 62.9% of
the engine state at the ThingsBoard guard. The largest exact candidates:
caller families (`cellsBySource` sets and maps 0.56 GB,
`changingByTarget` 0.18 GB); Target rows (one-element sets and the outer
map 0.37 GB, the `outgoingTargetRows` copy 0.09 GB); the unused
replacement indexes `indexedFlow` and `indexedConcrete` of the point
stores (0.30 GB); duplicate small key objects (0.42 GB); `PathTrie`
posting sets (0.47 GB).

**New.** The exact representation changes of the parent proposal N6
(small sets inline, shared keys, no empty maps, no unused indexes).

**Why it improves.** About 2.1-2.4 GB of engine state at the guard. It
moves the guard to about 6.5-7.0 M events; not enough alone.

## N9. A Work priority that counts block work

**Current.** `EventQueue` orders Work events by statement steps only. In
the Stirling-PDF stall one thread works for 820-850 s while 11-12 events
wait (report §10).

**New.** Add the block-runtime work units to the priority key, or serve
waiting events in turn after each quantum.

**Why it improves.** Hypothesis: the waiting events include callees of
the owner, so the owner works on old summaries and must work again later.
A census of the runner queue confirms it first.

## N10. An annotation index for rule resolution

**Current.** `TaintRulesStorage.configForMethod` takes 24% of ThingsBoard
run 1. Its own time is in `SerializedCondition$AnnotationConstraint.equals`,
`collectAnyArgumentClassifiers` and `resolve`: a linear scan of the
annotation constraints for each method.

**New.** Index the rule conditions by annotation type, so that a method
checks only the conditions of its own annotations.

**Why it improves.** The scan becomes a lookup. It shortens run 1 only;
it does not change the ThingsBoard memory wall.

## B1. Why R2 gives no progress

**Current.** The spec (§I.2) says that under the demand `x.[any](T)` the
forward start is cut one field below the entry (C2), so the finding of
PG stays provisional in each round, and R2 is needed. On the PG program
of the tests, R1 alone confirms the finding at run 2d+1, the same as
R1 + R2: run 1 starts `use` with the abstract `x.*`, and later forward
starts follow the field-limit schedule (report §6.2).

The real trace of the spec (§II.1) is Stirling-PDF
`AuthController#login`. With R2, the run frontiers of the complete
launch are the same as without R2 in each of the 11 runs (4,219 … 108
methods), and `login` is analysed in each run (report §6.2).

**New.**

1. A census on a proto branch for `login` and its entry point, per run:
   the backward seeds (literal or tree), the capture keys that the
   forward run stores at its sinks and sources, the forward hand-off rows
   and the rule of each row (seed, reversed source, record, C2 start).
   This tells which rows keep `login` in demand.
2. If the rows do not come from `[any]` seeds, §II.1 names the wrong
   cause: correct it and find the maker of the rows (no switch, no
   scope cut).
3. If they do come from `[any]` seeds: find why the tree seed does not
   go deeper (for example, the run-1 capture has only the root leaf, as
   in PG).
4. Find the code path of the C2 cut of §I.2 and build a test program
   where it binds. If no such program exists, correct §I.2 and §II.5 and
   decide whether R2 stays.

**Why.** R2 costs at most 0.66% of a run, but it adds a store and a
hand-off path. It must have a case that needs it.

## B2. The cause of the 2 provisional Stirling-PDF findings

**Current.** The complete Stirling-PDF launch has 2 provisional findings
(`java.security.xss#sink#1`, `UserController` lines 753 and 768), in
this build and in the parent. They are the only provisional findings on
the four projects.

**New.** A census on a proto branch for these two sinks: the rule
literals and tails, the backward seeds per run, the capture trees, and
the cut that keeps the fact DEMAND.

**Why.** If the literal is `[any]` and the run-1 capture is only the root
leaf (report §6.2), R2 starts one round late; if the cut is another one,
it shows which convergence rule is missing.

## M1. Open measurement: the Conductor run-2 heap

Conductor backward run 2 reaches 8,157 MB heap after GC of the 8,192 MB
heap (parent control: 8,173 MB), with 317 GC pauses in 48 s (report §7).
It is the memory peak of the launch and the nearest point to an OOM on
Conductor. No census of its owners exists. First step: a heap dump at the
run-2 peak (an event trigger, not `jmap`: a forced GC clears the soft
references) and the owner census of the ThingsBoard method. A proposal
follows from the census.

## Carried over: P4, P6-P8

The evidence of the earlier proposals did not change:

| # | Proposal | Evidence |
| --- | --- | --- |
| P4 | Do not repeat prescan work in run 1 | Run-1 alias analysis and rule resolution (parent report §7) |
| P6 | Joined-exit report location | The 8 Stirling-PDF location twins remain (report §3.1) |
| P7 | Smaller work units for a single-package project | OWASP run-1 window: about one analyzer core (report §8) |
| P8 | No lock around a rule-cache miss | Parent report §8.4 |

## Not proposed

- **Removal of R2 now.** It costs at most 0.66% of a run and changes no
  result. B1 decides it.
- **A pre-filter for `SeedIndex.sinkTree`.** The `CaptureKey` lookup is
  the largest R2 cost, but at most 4 samples per run.
- **Replay of saved records on the link delta only.** `replaySaved` is
  85-99% of the long backward runs, but the parent census found only
  0.02-0.04% (Stirling-PDF) and 0.7-2.7% (Conductor) of the offered
  leaves offered before on the same link. The cost is the restriction of
  each replay (N4, N8), not the replay of old leaves.
- **A change of `TrieNode.hashCode`, the P1 cohort form, stops on
  repeated hand-offs, GC tuning**: as in the parent proposal.

# Next iteration: P1, P2 and P3

Status: P3 LANDED (`0919c7500`); P2' LANDED (`ad7b06320`) AND REVERTED
(`c89881544`), 25 November 2026. The implementation followed
[next-iteration-p3-p2m-implementation.md](next-iteration-p3-p2m-implementation.md).
The landing measurement
([report](../docs/reports/bidirectional-p3-p2m-landing-20261125.md)) kept
all results for both rules. P2' failed the memory gate: about 0.9 KB of
live heap per memo entry, +0.8-1.4 GB of heap after GC in the long loop
runs, GC pauses +70% on Conductor.
Spec date: 25 November 2026. This spec follows
[design-guide.md](design-guide.md) and [proof-guide.md](proof-guide.md).
Source: proposals P1-P3 of
[bidirectional-next-iteration-20261125.md](../docs/design/bidirectional-next-iteration-20261125.md),
with the evidence of the
[group A landing report](../docs/reports/bidirectional-group-a-landing-20261125.md).

- Base: `saloed/bidirectional` at `c5702ba4f`. Its core is the measured
  group A build `5804e44dd`, so the landing measurements are the
  reference for every gate here.
- Prototype branch: `proto/p1-p3-20261125`:

  | Commit | Content |
  | --- | --- |
  | `2ad12e049` | flags, P3, P2 replay-once, P1 ablation 1 |
  | `9bf66a9b4`, `d42a3a330` | P2 census: offers per method, restriction inputs |
  | `d02954434`, `dfd716f71` | P1 census: callee and local answers |
  | `f3910bede` | P2' restriction memo |
  | `45be97ef2` | P1 ablation 2 |

- Flags: `opentaint.bidi.proto.p1|p2|p3|p2m|p1geo`, each `OFF`,
  `SHADOW` or `ON`. `OFF` is the native runtime.
  - `SHADOW` runs the native code and counts. For P3 and P2' it also
    computes the rule and compares.
  - `ON` uses the rule. For P1 (`p1`, `p1geo`), `ON` is a diagnostic
    ablation, and it is unsound.
- Campaign data: `/drive-testcomp/opentaint-go-rules/p1p3-spec-20261125/`
  (`projects/`, `unit-tests/`, `rule-suite/`, `analysis/`, `scripts/`).
- Proofs, in `spec/lean/ApSpec/`. All three are constructive and use
  only `propext` (P3 also uses `Quot.sound`):
  - `FlowGroupIncremental.lean` (P3);
  - `RestrictionMemo.lean` (P2');
  - `LoopReplayOnce.lean` (the withdrawn P2 rule).

## 0. Classification (design-guide rule 12)

| Id | Rule | Real trigger | Evidence | Class |
| --- | --- | --- | --- | --- |
| P3 | Incremental canonicalization in `FlowGroup.addAll` (§2) | Conductor runs 4-8 and Stirling-PDF runs 8/10: up to 28 M calls in a run; 58-89% of them change nothing, but each call does two full passes | Shadow: 0 mismatches in about 60 M calls. Prototype: results identical on 4 projects (Stirling-PDF 3 launches); Conductor runs 6-7 −10% and −35%; `addAll` profile share −52..−72%. Proof: `FlowGroupIncremental.lean` | **WI** |
| P2 | Replay each (link, value) pair once (§3.1-§3.4) | Proposed: repeated pairs in the loop-block stall | Shadow: repeated pairs are ≤0.002% of the replay time in the stalls. The rule is exact (`LoopReplayOnce.lean`), but it has no effect | **Withdrawn** (rule 7) |
| P2' | Per-run memo of the loop-output restriction (§3.6) | Conductor runs 4/6/8: 36-74% of the restriction time is on inputs restricted before (185 s of 258 s in run 8) | Shadow: 0 mismatches in 44 M calls. Prototype: results identical on Conductor, OWASP and Stirling-PDF (3 launches); Conductor run 4 −48%, runs 1-7 −13%; no fix of the Stirling-PDF stall. Proof: `RestrictionMemo.lean` | **WI** (repeat OWASP time on a quiet host at landing) |
| P2'' | Order of the loop-block local worklist (§3.6) | Stirling-PDF: the same hand-off gives 7 k or 562 k offers in run 9 | Census only; no stalled-order census | Not prototyped |
| P1 | One geometry with an exact mark set in run-1 (§4) | ThingsBoard run-1 OOM | Census: 16.2 marks per callee geometry. Ablation 2 removes 90% of the answers, and the OOM is unchanged (same events, same memory) | **Withdrawn** as an OOM fix; back to rule 1 |

The proposals P1-P3 assumed three causes. The measurements confirm one
(P3). They refute two (P2: no repeated pairs; P1: the mark repetition
does not drive the OOM). They find one new exact rule (P2'), and one
real trigger without a rule yet (P2'').

Landing, 25 November 2026: P3 is landed (`0919c7500`). P2' was landed
(`ad7b06320`) and reverted (`c89881544`). Both kept all results. P2' made
Conductor run 4 -51% and run 6 -19%, but its memo held about 0.9 KB of
live heap per entry: +0.8-1.4 GB of heap after GC in Conductor runs 6-8
and in the Stirling-PDF stall runs, and GC pauses of 34.5 s against
20.3 s on Conductor. The prototypes did not show this, because they had
no class histogram and no GC comparison per run.

## 1. Method and gate

The work followed design-guide rule 3, in this order:

1. Code map of each rule site.
2. Counters in shadow mode, on OWASP, Conductor and Stirling-PDF, in one
   launch (rule 4).
3. Ablation on the real case (rule 3.1).
4. A native prototype behind a flag, gated alone (rules 3.2 and 6):
   - module suite, jvm suite and rule suite;
   - the four reference projects;
   - three Stirling-PDF launches, because its stall depends on the
     order of work.
5. Proofs for each rule that can be WI (rule 13).

The gate of a rule (rule 6):

- The confirmed and provisional results are the same as the parent
  build. The parent is the group A landing measurement of the same core.
- All suites pass.
- Wall time and peak memory are not worse.

The prototype changes no rule text. A rule that fails its gate is
withdrawn (rule 7).

## 2. P3: incremental canonicalization in `FlowGroup.addAll`

### 2.1 Real trace

A FLOW group holds the FLOW values of one base, one premise and one
point. `FlowGroup.addAll` (`ap/Groups.kt:57-109`) adds one value. In the
landing launches it is the largest single share in the long tails:

| Project, run (landing report §7.1) | FLOW subsumption share |
| --- | ---: |
| Conductor run 6 | 40% |
| Conductor run-7 tail | 93% |
| Conductor run 8 | 36% |
| Stirling-PDF runs 8 and 10 (launch 1) | 48-56% |

The async-profiler windows of the same launches:

- `FlowGroup.addAll` is 10.5% of all samples in the Conductor run-8
  window and 12.5% at the time limit.
- Inside `addAll`, 78-86% of the samples are in `subtractSubsumed`
  called from the passes over all rows. 9-14% are in `insert`.
- The caller is the loop-block completion store
  (`MethodBlockRuntime.Entry.addCompletion` → `ScopedEdgeStore.addAll`)
  in 100% of these samples.

The shadow counters of this campaign (one launch,
`projects/counters/*/bidi/analyzer.log`) give the volume:

| Project, run | `addAll` calls | Insert changes nothing | Rows before the insert, mean / max |
| --- | ---: | ---: | --- |
| Conductor run 4 | 4,582,240 | 67.2% | 1.09 / 3 |
| Conductor run 6 | 28,320,481 | 57.7% | 1.04 / 4 |
| Conductor run 8 (timeout) | 7,618,684 | 89.1% | 1.19 / 5 |
| Stirling-PDF run 8 | 2,303,390 | 68.2% | 1.63 / 3 |
| Stirling-PDF run 10 | 2,384,381 | 69.5% | 1.66 / 3 |
| OWASP run 1 | 1,452,490 | 12.4% | 0.15 / 2 |

The groups are small: at most 5 rows. So the cost is not quadratic in
the rows. The cost is fixed work on each call:

- two full passes over all rows;
- a merge scan and a promotion scan;
- all of this also when the insert changes nothing (58-89% of the calls
  in the tails).

### 2.2 Current behavior

```text
addAll(t):                                   // ap/Groups.kt:57-109
  before = copy(list)
  insert(t)                                  // result ignored
  loop:
    list = [ subtractSubsumed(compactPacket(r), list − r) for r in list ]   // pass 1
    if mergeMustOverlap(list): continue
    p = promotion(list); if p == null: break
    insert(p)
  list = [ subtractSubsumed(compactPacket(r), list − r) for r in list ]     // pass 2 (final)
  return [ r − (old roots of before with the same group key) for r in list ]
```

`TaintGroup.addAll` (`ap/Groups.kt:204-224`) already returns early when
`mergeHeader` changes nothing. `FlowGroup.addAll` has no such return.

### 2.3 Rule P3

```text
addAll(t):
  before = copy(list)
  changed = insert(t)
  if changed == null and list has the same row objects as before:
    return []                                          // (a) the insert changed nothing
  clean = the row objects of before that are still in list
  loop:
    list = [ if r in clean: subtractSubsumed(r, rows not in clean)   // (b) only the changed rows
             else:          subtractSubsumed(compactPacket(r), list − r)
             for r in list ]
    clean = all rows of list
    if mergeMustOverlap(list): continue                // the merge makes new row objects
    p = promotion(list); if p == null: break
    insert(p)                                          // the insert makes new row objects
  return [ r − (old roots of before with the same group key) for r in list ]   // (c) no final pass
```

- (a) `insert` returns `null` when it changes nothing. It can also
  return `null` after it removes a redundant row (`Groups.kt:42`). Thus
  P3 also compares the row objects. When a row was removed, P3 does not
  return early.
- (b) A clean row is a row of the stored list, or a row of the last
  pass output, that no merge or insert replaced.
- (c) The final pass is deleted.

The merge scan, the promotion scan, the row order and the returned
delta do not change.

### 2.4 Why the rule is exact

The pass subtracts covers point by point. `LeafAlgebra.subtract`
(`ap/TrieOps.kt:452-492`) removes from each leaf the union of two
things:

- the `at` leaf of the stored row at the same position;
- the `below` leaves of the stored row above that position, through an
  admitted first step.

So the cover of one position is a union over the leaves of the stored
row. `compactPacket` removes a position that a leaf above it in the same
row covers. Three facts follow:

1. **A pass is idempotent.** A row of a pass output is compact. No other
   row of the output covers any of its positions, because an output row
   has fewer positions than its input row and cover is monotone. So a
   second pass changes nothing. The native loop ends right after a
   pass, so the final pass changes nothing (c).
2. **A stored list is a fixpoint.** `addAll` stores a pass output on
   which merge and promotion found nothing. If the next insert changes
   nothing, the loop and the final pass give the stored list again, and
   the delta is empty (a).
3. **Clean rows need only the changed rows.** A clean row is compact,
   and no other clean row covers it. Its pass result is therefore the
   row minus the covers of the changed rows (b).

The Lean module `ApSpec/FlowGroupIncremental.lean` proves these facts:

| Theorem | Statement |
| --- | --- |
| `pass_out_clean`, `pass_idem` | A pass output row is compact and not covered; the pass is idempotent |
| `final_pass_noop` | The final pass after the loop changes nothing |
| `exit_fixpoint` | The list that the loop gives (when it exits) is a fixpoint: pass, merge and promotion change nothing |
| `passInc_eq` | When the clean rows are compact and pairwise not covered, the incremental pass equals the full pass |
| `loopInc_eq` | The incremental loop equals the native loop |
| `addAllInc_eq` | On every stored fixpoint, the P3 `addAll` gives the native list |

Two runtime checks agree with the proofs:

- **Shadow mode.** It runs both forms on every call of three projects,
  about 60 M calls. There are 0 list mismatches and 0 delta mismatches.
  The native final pass changed the list 0 times.
- **Property test.** `ProtoP3FlowGroupIncrementalTest` runs 3,000 random
  insertion sequences: both layers, all FLOW tails, field and mark
  exclusions. The results are equal.

### 2.5 Prototype result

Prototype `2ad12e049` with `opentaint.bidi.proto.p3=ON`. Every launch
had the profile windows of the landing campaign. The reference is the
landing measurement of the same core (landing report §4-§5).

**Suites (P3 alone).**

| Suite | Result |
| --- | --- |
| Module suite | 2,775 tests, 0 failures (2,774 native tests and the new property test) |
| jvm suite | 474 tests, 0 failures |
| Rule suite, bidirectional mode | 786 success, 0 false positive, 0 false negative, 0 skipped (22 disabled, as native) |

**Projects.**

| Project | Parent: status, engine s, peak RSS GiB | P3: status, engine s, peak RSS GiB | Results against the parent |
| --- | --- | --- | --- |
| OWASP | OK, 121.0, 9.52 (wall 197.1 s) | OK, 122.4, 9.44 (wall 194.0 s) | 2,633 = 2,633; code flows identical |
| Conductor | TIMEOUT in run 8; runs 1-7: 652.5 s; 10.26 | TIMEOUT in run 8; runs 1-7: 576.0 s; 10.15 | SARIF byte-identical |
| ThingsBoard | OOM in run-1 at 4.69 M events | OOM in run-1 at 4.41 M events | No results (both) |
| Stirling-PDF, 3 launches | Launch 1 OK (load 22); launch 2 TIMEOUT in run 9; launch 3 TIMEOUT in run 11; 9.49-10.11 | TIMEOUT in run 11 (3 of 3); 9.75-10.48 | SARIF byte-identical to parent launches 2 and 3 (32 results) |

Run times where P3 acts (engine seconds):

| Run | Parent | P3 |
| --- | ---: | ---: |
| Conductor run 6 | 374.6 | 336.2 (−10%) |
| Conductor run 7 | 96.1 | 62.3 (−35%) |
| Conductor run 4 | 106.6 | 103.5 |
| Stirling-PDF run 8 (mean of the quiet launches) | 17.6 | 14.1 (−20%) |
| Stirling-PDF run 10 | 17.1 | 14.8 (−13%) |
| Stirling-PDF run 9 (the stall) | 893.8+ / 399.4 | 597.3 / 181.4 / 426.3 |

Profile windows (share of all samples in `FlowGroup.addAll`):

| Conductor window | Parent | P3 |
| --- | ---: | ---: |
| Run 6 | 5.4% | 1.5% |
| Run 8 | 10.5% | 3.6% |
| At the time limit | 12.5% | 6.0% |

The new top frames in Conductor runs 6 and 8 are the C5 admission of
the loop restriction (`RestrictedInitialPolicy.fitsBudget`, `emit`).

- **Effect.** P3 removes most of the FLOW-subsumption cost. Conductor
  reaches run 8 76 s earlier.
- **No fix.** P3 does not end the Conductor timeout or the Stirling-PDF
  stall. Those are replay work (§3).
- **No effect on OWASP and ThingsBoard.** Their FLOW groups are almost
  empty in run-1 (0.15 rows per call on OWASP).

ThingsBoard: the P3 launch and the P1 ablation launch used the same
options, and they stopped at 4.41 M and 4.42 M events. The parent launch
used the heap-snapshot option and stopped at 4.69 M events. With one
launch per arm, this difference is not a P3 effect.

Peak RSS is in the range of the parent launches. One Stirling-PDF
launch is 0.37 GiB above the highest parent launch, and the other two
are inside the range. The maximum heap after GC is not higher
(6,704-7,079 MB, parent 6,732-6,783 MB).

### 2.6 Execution site and volume

- **Where it runs.** Once per `FlowGroup.addAll` call, which is once
  per FLOW value that enters a store.
- **Volume.** Up to 28.3 M calls in one run (Conductor run 6).
- **New work per call:**
  - an identity comparison of at most 5 row objects;
  - when the insert changed something, an identity set of at most 5
    rows.
- **Removed work:**
  - on a call whose insert changes nothing (58-89% in the tails): the
    whole loop, the final pass and the delta;
  - on every other call: the final pass, and the subtraction of a clean
    row by other clean rows.

### 2.7 Semantic scope

- Changed: nothing. P3 is a pure optimization. The stored rows, their
  order and the returned delta are the native ones (§2.4).
- Unchanged: field transfer, premise matching, layers, sources and sinks,
  `TaintGroup`, the merge and promotion rules, and the stores that call
  `addAll`.

### 2.8 Proof scope and the differences between model and production

| Model | Production | Check |
| --- | --- | --- |
| A row is a list of positions | A row is a trie with shared nodes | Cover is defined per position; `subtract` is pointwise (§2.4) |
| `covAt` and `dom` are parameters | `at`/`below`/`admits` of `subtractSubsumed`, and `compactPacket` | The theorems need only that cover is a union over the stored leaves. They do not need its exact form. Property test |
| A row has an `id` | Object identity (`it !== row`) | The prototype compares identities |
| `merge`, `promote` and `insert` are abstract | `mergeMustOverlap`, the promotion scan, `insert` | The theorems need only: the loop ends after a pass; merge and insert make new rows |
| The loop has fuel | The loop ends by the comment at `Groups.kt:61-62` | Not proved here |
| `insert = none` means "no change" | `insert` can return `null` after it removes a row | P3 compares the row objects (§2.3 (a)) |

**Adversarial review (design-guide rule 10).** A reviewer tried to break
P3 against the code and found no counterexample. It checked:

- that subtraction is pointwise and order-independent;
- that a pass output row is compact and not covered;
- that unchanged rows keep their object identity;
- that the merge and promotion scans read only the list;
- that only `insert`, `addAll` and `mergeMustOverlap` write the store.

Residual risks for the landing:

- A cancellation in the middle of `addAll` leaves a list that is not a
  fixpoint. Native repairs it on the next call, and P3 does not. This is
  harmless today, because a cancelled run ends the analysis and the
  first checkpoint throws before any write.
- Any new writer of `trees` (a restore or a bulk load) must store a
  fixpoint, or P3 is no longer exact. The landed code must state this
  invariant at the field.
- The property test uses one base, three fields and depth 3 or less. It
  does not measure how often it reaches the promotion path.

### 2.9 Withdrawal condition

Withdraw P3 when any of these occurs:

- a confirmed or provisional result is different from the parent;
- a shadow mismatch occurs;
- a suite fails;
- wall time or peak memory is worse on a project.

### 2.10 Classification

**P3 is WI.**

- The prototype gives the parent results on all four projects and all
  suites.
- It removes 52-72% of the FLOW-subsumption samples, and it makes
  Conductor runs 6-7 faster.
- It has no negative consequence that this campaign measured.
- The proofs are in §2.4.

The landed form has no flag and no counter
(`feedback-implement-without-flags`). It deletes the native final pass.

## 3. P2: loop-block replay

### 3.1 The proposal

Proposal P2 says: "Replay each (offered value, saved record) pair once.
A new value replays all records, a new record replays all values." It
assumes that the stall repeats replays of the same pairs. It expects
that the work then does not depend on the order of the offers.

### 3.2 Code facts

- **Offer.** An offer is a (`LocalLink`, `Facts`) pair at
  `MethodBlockRuntime.offerChild` (`engine/MethodBlockRuntime.kt:343`).
  `offerChild` calls `replaySaved` on each offer, before the link store
  removes duplicates (`:357`, `:375`).
- **Records are frozen for the run.** `config.records` is a read-only
  view (`store/RecordStore.kt:229-236`). The driver writes records only
  at the barrier (`driver/IterationDriver.kt:215-216`). The proposal's
  case "a new record replays all values" thus never occurs in a run.
- **One replay is a function of the offer.** It reads only frozen run
  inputs and pure caches:
  - the records, the saved targets and the demand snapshot;
  - the admission policy;
  - the restriction session, which is new per call;
  - the observers and the query scratch.

  Its writes go to stores that only grow in a run. These are the
  completion store, `rawTargetRows` and `KaryJoin.add`, and a value that
  is already stored gives no fresh delta.

So it is exact to replay an equal (link, value) pair only once. The Lean
module `ApSpec/LoopReplayOnce.lean` proves this for a worklist with
offers, a pure replay and stores that only grow. Its theorem is
`runOnce_eq`: after any number of steps, the store and the worklist are
the native ones.

### 3.3 Shadow measurement: the pairs do not repeat

The counter launch (P2 `SHADOW`) replays every offer and counts the
pairs that it saw before:

| Project, run | Offers | Repeated pairs | Replay time | Time of repeated pairs | Engine time |
| --- | ---: | ---: | ---: | ---: | ---: |
| Stirling-PDF run 9 | 562,128 | 89 | 339.9 s | 1.8 ms | 404.3 s |
| Stirling-PDF run 11 (timeout) | 245,204 | 94 | 517.8 s | 2.8 ms | 521.6 s |
| Conductor run 6 | 222,189 | 134 | 118.7 s | 1.7 ms | 424.8 s |
| Conductor run 8 (timeout) | 130,227 | 255 | 308.2 s | 3.2 ms | 304.7 s |
| Conductor run 4 | 118,019 | 176 | 16.2 s | 10.8 ms | 111.2 s |

Replay time is summed over the workers. A stall has one busy worker, so
the replay time can be near the engine time.

- In the stalls the replay of repeated pairs is 0.002% of the replay time
  or less.
- Few offered leaves were offered before on the same link
  (`leavesSeen`): 0.02-0.04% in Stirling-PDF runs 9 and 11, and
  0.7-2.7% in Conductor runs 6 and 8. Most offers are one leaf.
- The shadow replays of repeated pairs gave 0 fresh completions. This
  agrees with §3.2.

The stall is not a repetition of pairs. It is a very large number of
**different** offers, for example 562,128 in Stirling-PDF run 9. Each one
has an expensive replay: 0.6 ms on average there, and 2.4 ms in
Conductor run 8. Replay is 84% of the engine time of Stirling-PDF run 9,
and almost all of the time of the timed-out runs.

### 3.4 Classification of the proposed rule

The "replay once per pair" rule is exact, but it removes no measurable
work. By design-guide rule 7 it is withdrawn. It is not WI, and it is
not implemented.

### 3.5 What the stall is

The P2 census (`d42a3a330`, P2 `SHADOW`) counts per method:

- the offers and their replay time;
- the fresh completions;
- the depth histogram of the offered values;
- the loop-output restriction calls and their distinct inputs.

The restriction input is the tuple (method, parent scope, loop, exit,
original, bounded value, gate). By §3.2 the restriction result is a
function of this tuple and the frozen run inputs.

**The same hand-off gives 80 times more offers in another order.** The
first census launch of Stirling-PDF took the fast order and completed
in 203 s. The counter launch took the slow order:

| Stirling-PDF | Slow order (counter launch) | Fast order (census launch 1) |
| --- | ---: | ---: |
| Run 7: offers / engine time | 54,806 / 22.6 s | 6,835 / 2.2 s |
| Run 9: offers / engine time | 562,128 / 404.3 s | 6,988 / 4.0 s |
| Run 11: offers / engine time | 245,204 / 521.6 s (timeout) | 7,637 / 3.2 s |
| Status | TIMEOUT in run 11 | OK after run 11 |

- The confirmed results are the same in both orders (32). The fast
  order also publishes the 2 provisional results, because it ends
  normally.
- In the fast order the stall owner `EmlProcessingUtils#decodeMimeHeader`
  gets 2,891 offers in run 9. 1,083 of them give at least one fresh
  completion.
- The offered values are short: depth 0-5, and depth 2 is most
  frequent.

So in the slow order about 98.8% of the run-9 offers are work that the
fast order does not do, for the same result. Each of these offers is a
different value. This is the order dependence of the landing report
§9.

**Restriction inputs repeat.** In the fast order:

| Stirling-PDF run | Restriction calls | Distinct inputs | Restriction time | Time on repeated inputs |
| --- | ---: | ---: | ---: | ---: |
| 8 | 81,078 | 19,374 | 2.8 s | 1.4 s |
| 9 | 55,262 | 16,539 | 3.0 s | 1.7 s |
| 10 | 73,136 | 16,403 | 2.6 s | 1.3 s |

About 70-80% of the restriction calls repeat an input seen earlier in
the run. They take 50-55% of the restriction time.

**Conductor** (census launch, the parent order; it times out in run 8
as before):

| Conductor run | Offers | Replay time | Restriction calls | Distinct inputs | Restriction time | Time on repeated inputs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 4 | 118,063 | 15.1 s | 4,840,262 | 829,201 | 73.3 s | 54.3 s |
| 6 | 216,251 | 113.1 s | 24,806,921 | 2,426,468 | 162.9 s | 58.3 s |
| 8 (timeout) | 205,580 | 377.2 s | 10,652,974 | 2,829,042 | 258.3 s | 184.8 s |

- Two contexts of `ParametersUtils#replace` hold most of the run-8
  offers: 91,234 and 91,720 offers, with 190 s and 182 s of replay.
- 32% of their offers give a fresh completion.
- The offered values have depth 0-5, and depth 4 is most frequent (the
  field limit is 7).
- 74% of the run-8 restriction time is on inputs that the run restricted
  before.

A second Stirling-PDF census launch also took the fast order (OK after
143.9 s). Thus this campaign has no census of a stalled Stirling-PDF
order. Of the 12 Stirling-PDF launches of this core:

- 4 took the fast order: landing launch 1 (load 22), the two census
  launches (P2 `SHADOW` only, no profiler) and P2' launch 1 (with
  profile windows);
- 8 took the slow order: landing launches 2-3, the counter launch, the
  three P3 launches and P2' launches 2-3.

The cause of the order choice is not known (§8).

### 3.6 Next step for P2

The census gives two directions. Only the first one has a native
prototype in this round.

**P2' — a per-run memo of the loop-output restriction.**

```text
current: onApplied → restriction.restrict(run1, gate, bounded, session)     // per applied value, every time
P2':     key = (parent scope, loop, exit, original, bounded value, gate)
         memo[key] ?: restriction.restrict(...).also { memo[key] = it }      // per method runtime, per run
```

- **Why it is exact.** The restriction reads the observer of
  (parent scope, loop). That observer reads only frozen run inputs: the
  demand scope views, the records, the saved targets, the layout, the
  live locals and the end rules. It also reads pure caches
  (`LoopQueryScratch`, prepared plans), whose answer does not depend on
  whether they are present. The restriction session is new per call. So
  the result is a function of the key. The memo is a cache of a pure
  function in one run. A miss recomputes, so a soft or bounded memo is
  still exact.
- **Prototype.** `f3910bede`, flag `opentaint.bidi.proto.p2m`:
  - a soft per-runtime map with at most 1 M entries, cleared when it is
    full;
  - `SHADOW` recomputes on every hit and counts mismatches.

**Prototype result** (`f3910bede`, P2' alone):

| Gate | Result |
| --- | --- |
| Module suite | 2,776 tests, 0 failures |
| jvm suite | 474 tests, 0 failures |
| Rule suite, bidirectional | 786 success, 0 false positive, 0 false negative, 0 skipped |
| Conductor, `SHADOW` (a hit is recomputed and compared) | 0 mismatches in 44 M restriction calls; SARIF byte-identical |

Memo hits in the `SHADOW` launch of Conductor:

| Run | Calls | Hits | Hit share |
| ---: | ---: | ---: | ---: |
| 4 | 4,845,271 | 4,012,378 | 83% |
| 6 | 25,396,994 | 22,741,995 | 90% |
| 7 | 2,661,213 | 2,307,647 | 87% |
| 8 (timeout) | 9,560,307 | 3,945,041 | 41% (the full memo was cleared 4 times) |

Run 8 has 2.8 M distinct keys, and the prototype clears its memo at
1 M entries. So run 8 loses most of its hits.

| Project | Parent | P2' `ON` | Results against the parent |
| --- | --- | --- | --- |
| Conductor | TIMEOUT in run 8; runs 1-7 652.5 s; peak RSS 10.26 GiB | TIMEOUT in run 8; runs 1-7 568.1 s; peak RSS 9.91 GiB | SARIF byte-identical |
| OWASP, launch 1 (quiet host) | OK; engine 121.0 s (run 1 76.2 s, runs 2-11 36.1 s); 9.52 GiB | OK; engine 130.2 s (run 1 82.7 s, runs 2-11 38.9 s); 9.64 GiB | 2,633 = 2,633; code flows identical |
| OWASP, launch 2 (host load 10 from another user) | — | OK; engine 161.2 s (run 1 103.7 s) | identical; time not representative |
| Stirling-PDF, 3 launches | 1 OK, 2 TIMEOUT (run 9, run 11) | launch 1 OK (engine 96.6 s); launch 2 TIMEOUT in run 9; launch 3 TIMEOUT in run 11 | SARIF byte-identical to the parent launch with the same end (34 when OK, 32 at TIMEOUT) |

| Conductor run | Parent engine s | P2' engine s | `restrict` share of samples, parent → P2' |
| --- | ---: | ---: | --- |
| 4 | 106.6 | 55.8 (−48%) | 37.0% → (no window) |
| 6 | 374.6 | 344.4 (−8%) | 30.0% → 15.6% |
| 7 | 96.1 | 93.3 | — |
| 8 (timeout) | 386.7 | 471.3 (timeout) | 33.5% → 20.0% |

- **Conductor.** The memo removes about half of the restriction samples.
  Run 4 is 48% faster. Runs 1-7 are 13% faster (568.1 s against
  652.5 s). Run 8 still times out.
- **Stirling-PDF.** P2' does not remove the stall: 2 of 3 launches stall
  in run 9 or run 11, as in the parent. The stall is the number of
  offers (P2''), not the restriction of each offer.
- **OWASP.** Launch 1 ran on a quiet host (mean load 3.0, the same as the
  parent).
  - Its engine time is 9.2 s longer. Of this, 6.5 s is in run 1, where
    P2' is inactive (no memo in run 1).
  - Runs 2-11 are 2.8 s longer.
  - The memo volume of OWASP runs 2-11 is 255 k calls, with 60-75%
    hits. Each call costs one key allocation and one hash lookup, so the
    memo itself costs well below 0.1 s.
  - The difference is therefore launch noise of the size seen in run 1.
    Launch 2 had external load and is not used.
- **Memory.** Peak RSS is 9.53-9.91 GiB, inside the parent range. The
  memo is soft, and it was never cleared by the GC in these launches
  (`softCleared=0`).

**Execution site and volume.** P2' runs once per restricted loop output
(`onApplied`, loop child, non-negative exit). The largest volume is
25.4 M calls in Conductor run 6. New work per call: one key and one
hash lookup. Removed work per hit: one `restrict` (baseline
observation, budget trials, C2/C5 queries).

**Semantic scope.** Changed: nothing. The memo returns the value that
`restrict` returns (proof and shadow). Unchanged: the restriction rule,
the loop blocks, the stores and the reports.

**Proof scope.** `RestrictionMemo.lean` proves that a sound memo
returns `f` for every sequence of calls and clears. It assumes that the
restriction is a function of the key in one run. This assumption is the
code reading above, and the Conductor `SHADOW` launch checked it (0
mismatches in 44 M calls). The model does not cover a key whose `Facts`
equality differs from the semantic value. Production uses structural
`Facts` equality, which includes the layer and the protection.

**Adversarial review (design-guide rule 10).** A reviewer tried to break
P2' against the code and found no counterexample. It checked:

- that `link` is used only by the trace;
- that the session has no hidden state (`certifiedFirstBudget` returns
  null; the precision cursors are not called);
- that the observer reads no `parent.state`, completions, `starts` or
  `preparedExits`;
- that `restrict` does not re-enter `onApplied`;
- key equality: interned premises, structural `Facts` with layer and
  `nonSubsumable`;
- that the cached list is a fresh, read-only list in a stable order.

Residual risks:

- **Cache-dependent branches.** These paths differ with and without the
  quantum scratch:
  - the prepared C5 plan or native C5;
  - `skipEmptyDataReplay`;
  - the probe with cached or fresh initials.

  The memo is exact only if these give equal observations. Native
  already assumes this, but no code enforces it. If it ever failed, the
  memo would fix the first answer for the run. The shadow run is partial
  evidence: a hit is usually recomputed under another scratch.
- **Diagnostics.** Hits skip `restriction.statistics` and
  `queryCounts`, so these counters differ between arms. The results do
  not.
- **Future changes.** Turning on certificates or precision cursors
  requires this audit again.

**Withdrawal condition.** Withdraw P2' if a shadow mismatch occurs, if a
result changes, or if a quiet OWASP launch at landing shows a time
regression in runs 2-11 that is larger than the noise of run 1.

**Classification: P2' is WI.** It is exact, it gives the parent results
on all projects and suites, and it makes Conductor faster. It does not
fix the Stirling-PDF stall. The landing gate must repeat OWASP on a
quiet host.

**P2'' — order of the loop-block local worklist (not prototyped).** The
same hand-off gives 7 k or 562 k offers. The next iteration must first
find what the 555 k extra offers are, in a stalled launch:

- per-offer samples;
- whether a later offer at the same link subsumes the value;
- which order the fast launch used.

A rule that only changes the order keeps the results if the local
fixpoint is confluent. The landing and this campaign show the same
confirmed results in both orders, but this is not proved.

## 4. P1: one geometry with an exact mark set in run-1

### 4.1 Real trace

ThingsBoard run-1 (forward, field limit 1) stops with OOM in every
launch. The landing report has the heap census (§8):

- The guard snapshot holds 11.38 GB. Run-1 engine state is 6.28 GB.
- The census found 17.07 M point memberships. 85% are TAINT DEMAND.
- `CallerInputValues` has 3.17 M slots (1.52 GB). One caller family has
  14.7 marks. 99.6% of the caller mark pairs keep the same mark.
- A diagonal point row has 17.4 marks.
- `PublicationIndex.targets` has 1.59 M DemandTarget premises, all
  concrete.
- The live heap grows by about 1.1 KB per event. The guard fires at
  4.69 M events.

### 4.2 Current behavior

- **A run-1 concrete premise has one mark.** `InitialAp` has
  `MarkSlot.Concrete(mark)`. No premise holds a `MarkSet`
  (`ap/Premise.kt:22-50`, `ap/Facts.kt:59-65`).
- **Answers are made one mark at a time.** `forEachConcreteAnswer`
  (`engine/Run1RequestMatching.kt:34-75`) makes one initial per
  matching mark, per trie node, per branch and per request row. It has
  two callers:
  - `SubscriptionManager.joinRequests` (callee answers, `:167-175`);
  - `Run1Abstraction` (local answers, `:44`).
- **Some parts already use one geometry and a mark mask:**
  - `NeutralRelationBatch` (a diagonal cohort: shape, template, marks);
  - `DiagonalRelations` rows;
  - `CallerMarkRelations` families.

  A cohort crosses only a plain point. A call, a loop block, an end or a
  non-neutral statement decodes it, one mark per event
  (`engine/BlockRunState.kt:590-612`).
- **These structures still have one entry per mark:**
  - premises and initial stores;
  - subscriptions;
  - `CallerInputValues` slots;
  - `PublicationIndex` rows and targets;
  - `TargetSummary` rows.

### 4.3 Ablation 1: one mark per answer group

The ablation (P1 `ON`, unsound, diagnostic only) emits only the first
mark of each (trie node, branch, request row) answer group.

| ThingsBoard | Native (landing) | Ablation |
| --- | --- | --- |
| Run-1 status | OOM; the guard fired 190.4 s into run-1 (4.69 M events) | OOM; run-1 ended after 174.5 s (4.42 M events) |
| Answer groups in run-1 | — | 3,359,265 |
| Concrete answers (all matching marks) | — | 3,360,581 (max 19 in one group) |
| Groups with more than one mark | — | 215 |

The answer groups have 1.0004 marks on average. The ablation therefore
removes 0.04% of the answers, and the OOM does not change. **The
request-row split is not where the marks multiply.** Each input fact
already has one mark under its own premise, so the repetition comes
from upstream.

The counter launch of ThingsBoard failed in the prescan (the legacy
engine) with "Prescan jobs have not joined". The prescan has no
prototype code. This is the known prescan hang.

### 4.4 Census and ablation 2: one mark per callee geometry

The P1 census (`dfd716f71`, P1 `SHADOW`) counts the run-1 answers at the
two answer sites. It uses 64-bit hashes of two keys:

- (method, base, path, tail, layer), the geometry;
- (method, base, path, tail, layer, mark).

One ThingsBoard launch, OOM in run-1 at 4.42 M events:

| Site | Answers | Distinct (geometry, mark) | Distinct geometries | Marks per geometry |
| --- | ---: | ---: | ---: | ---: |
| Local answers: `Run1Abstraction.emit` → `addInitial` | 3,361,168 | 430,914 | 26,630 | 16.2 |
| Callee answers: `SubscriptionManager.joinRequests` | 76,089 | 26,541 | 3,762 | 7.1 |

- **The repetition is at the callee admission.** `Run1Abstraction.emit`
  runs once per caller input, which is once per caller premise. Each
  caller premise has its own one-mark fact. So one callee geometry gets
  one concrete initial per caller mark: 16.2 marks on average. This
  agrees with the heap (14.7 marks per caller family, 17.4 per diagonal
  point row).
- **Most answers are duplicates.** 87% of the local answers repeat a
  (method, geometry, mark) answer of the run. `addInitial` removes them
  (`InitialFactStore`), but each one still costs one answer pass.
- The first ablation cut per request row, which is the wrong unit, so it
  removed nothing.

**Ablation 2** (`45be97ef2`, `opentaint.bidi.proto.p1geo=ON`,
diagnostic and unsound) keeps only the first mark answered for each
(method, geometry, layer).

| ThingsBoard run-1 | P1 census (native behavior) | Ablation 2 |
| --- | ---: | ---: |
| Answers kept / dropped | all | 334,574 / 2,945,734 (90% dropped) |
| Distinct (geometry, mark) answers, local | 430,914 | 32,310 (= distinct geometries) |
| Status | OOM | OOM |
| Events when run-1 ended | 4.42 M | 4.38 M |
| Memory at 4.1-4.4 M events | 10.8-11.0 GiB | 10.8-11.2 GiB |
| Events in flight in the last 60 s | 21,000-22,000 | 47-178 |

- **The ablation removes the repetition, but the real case does not
  change.** With one mark per callee geometry, run-1 still reaches the
  memory guard at about 4.4 M events. Memory against events is the same.
- **What changes is the queue.** The queue is almost empty in the last
  minute (47-178 events in flight against about 21,000). The remaining
  work is a chain of events, not a broad front. With one launch, it is
  not known whether run-1 was near its end.
- **Conclusion.** The per-mark initials do not drive the run-1 memory of
  ThingsBoard. A mark-set premise (§4.5) cannot fix the OOM alone, even
  if it removes all of this repetition. The ablation is an upper bound,
  because it drops 90% of the answers and therefore much downstream
  work.

### 4.5 Design for the next iteration

This section is a design to prototype. It is not a rule yet.

**Idea.** Use the existing diagonal cohort form across the call boundary.
In this form one geometry carries an exact mark mask
(`NeutralRelationBatch`, `DiagonalRelations`, `CallerMarkRelations`).
A cohort (shape `g`, template `T`, marks `S`) means the set of
per-mark premises {(g, m) | m ∈ S}. Under premise (g, m), the fact is
`T` with every mark replaced by {m}. It is not a new abstraction: the
cohort holds every per-mark premise.

```text
current (per mark):                         new (per cohort):
  caller premises (g', m1..mk)                caller cohort (g', S)
  k answers (g, mi) to the callee             one answer (g, S) to the callee
  k initials, k start facts                   one cohort start (shape g, template, S)
  k publications                              one diagonal publication (g → T, mask S')
  k caller slots, k DemandTargets             one family slot (S), one DemandTarget (g, S)
```

**Split points.** A cohort splits only at a step that reads a mark (the
step list is in §4.2):

- a cleaner with selected marks;
- a mark check, and the R1 mark policy;
- a source condition or a conjunction (`PremiseSet`, `KaryJoin`);
- a sink witness;
- a pass or GEN rule with a mark literal;
- `markSubPart` against a concrete callee publication;
- the protection rules that read premise marks (`ApOps.applyEdge`,
  `applySummary`, `applyRecordLeaf`, `ruleProtection`).

A step that names k marks splits a cohort into at most k + 1 classes:
each named mark, and the rest. It never splits into |S| classes.

**Proof obligation** (proof-guide.md): for each step kind `f`,
`decode(f_cohort(c)) = ⋃ m ∈ S . f(decode_m(c))`.

- Two modules already prove this for the in-method neutral steps:
  `Run1WorkBatchingClosure.lean` and the `FlowBacked*` modules.
- New obligations:
  - the answer join;
  - the call binding and the return;
  - the publication application;
  - the target emission and the relay;
  - each split point above.

**Gate.** ThingsBoard run-1 completes within 12 GiB. OWASP, Conductor
and Stirling-PDF give identical results. All suites pass.

### 4.6 Classification

P1 is **not WI**, and it is withdrawn as a fix for the ThingsBoard OOM
(design-guide rule 7):

- Ablation 1 shows that the proposed cut point, the answer split per
  request row, does not multiply marks.
- The census finds the real repetition: 16.2 marks per callee geometry
  at the callee admission.
- Ablation 2 removes that repetition, and the OOM stays at the same
  event count and the same memory.

The design of §4.5 stays as a possible cost reduction. It removes up to
94% of the run-1 initials (430,914 → 26,630). It is not a memory fix,
and it is not proposed for the next iteration without a new trigger.

**Next step (rule 1).** Find what fills the run-1 heap when the per-mark
answers are gone:

1. Take one heap snapshot of ablation 2 at the guard, with the
   `--heap-snapshots` option of the harness.
2. Use the census method of the landing report §8: owners, membership
   shapes, growth per event.
3. Count the run-1 events per kind: source, call, return, static,
   request, DEMAND.

This finds the event source that grows with the run.

## 5. Plan for the next iteration

In order of the evidence:

1. **Land P3.**
   - Write an implementation proposal ([impl-proposal-guide.md](impl-proposal-guide.md))
     from §2.3. No flag, no counter.
   - The property test `ProtoP3FlowGroupIncrementalTest` becomes a plain
     unit test against a copy of the native algorithm in the test tree.
   - `FlowGroupIncremental.lean` is the proof.
   - Gate after landing: the full measurement of §1.
2. **Land P2'.**
   - Implement the per-run memo of §3.6 in `MethodBlockRuntime`, without
     a flag and without a counter.
   - The implementation proposal chooses the memo bound. A soft
     reference keeps exactness, and a miss recomputes.
   - Conductor run 8 has 2.8 M distinct keys. The prototype cap of 1 M
     entries cleared the memo 4 times there, so a larger bound can give
     more hits. Measure the heap for the chosen bound.
   - `RestrictionMemo.lean` is the proof.
3. **P2'' (order).** First a stalled-order census of Stirling-PDF:
   - per-offer samples;
   - subsumption between offers on the same link;
   - the order of the first 10 k offers of the stall owner, in a fast
     and in a slow launch.

   8 of 12 launches took the slow order, so about three launches give
   one stall. Then design an order rule and its confluence argument.
   Prove it before any measurement claim.
4. **P1.** Go back to rule 1:
   - one heap snapshot of ablation 2 at the guard;
   - the landing §8 census method;
   - run-1 events per kind.

   No P1 rule is proposed before a new trigger is found. The mark-set
   design of §4.5 stays a cost idea: up to 94% fewer run-1 initials.
5. **Measure the combination.** P3 and P2' act on the same Conductor
   runs. Measure them together after they land. Their effects were
   measured alone only.

## 6. Semantic scope

- **P3.** Changed: nothing (a pure optimization of one store).
  Unchanged: everything else (§2.7).
- **P2 replay-once.** Withdrawn. It changes nothing.
- **P2'.** Changed: nothing (a cache of a pure function in one run).
  Unchanged: the restriction rule and everything else (§3.6).
- **P1.** No rule in this round. The design of §4.5 must keep the
  per-mark meaning of every premise. A cohort is a set of per-mark
  premises, not a new abstraction. GROUP mode is not this design,
  because it loses which mark is present.

None of the prototypes changes data-class equality or hashing of a stored
value. The P2 census adds `Pair<LocalLink, Facts>` keys in a
prototype-only set.

## 7. Checklist

```text
[x] Failure class and real trace: P3 §2.1, P2 §3.3 and §3.5, P1 §4.1 and §4.4
[x] Ablation on the real case: P1 ablations 1 and 2 (§4.3, §4.4); P3 and P2' are exact, so the
    shadow modes replace an ablation (§2.4, §3.6)
[x] Native prototype: P3 (OWASP, Conductor, ThingsBoard, Stirling-PDF x3); P2' (Conductor shadow and ON,
    OWASP x2, Stirling-PDF x3); P1: ablations only
[x] Execution site and measured volume: P3 §2.6; P2' §3.6; P1 §4.4
[x] Semantic scope: §6
[x] Proof scope and model differences: P3 §2.8; P2 and P2' §3.2, §3.6
[x] Withdrawal condition: P3 §2.9; P2' §3.6; P2 replay-once withdrawn (§3.4); P1 withdrawn (§4.6)
[x] WI classification: header
[x] Proofs: FlowGroupIncremental.lean (P3), RestrictionMemo.lean (P2'), LoopReplayOnce.lean (P2,
    withdrawn rule)
```

## 8. What was not measured, and weak verdicts

- **Launch counts.** OWASP, Conductor and ThingsBoard have one launch per
  arm (design-guide rule 6). Stirling-PDF has three launches for P3 and
  for P2'.
- **The order of Stirling-PDF.** It took the slow order in 8 of 12
  launches of this core. The cause of the order choice is not known.
  Profile windows do not force it (P2' launch 1 had them and was fast).
- **No census of a stalled order.** The census launches did not stall.
  So the shape of the 555 k extra offers is not known (§3.6, P2'').
- **The parent reference.** The parent numbers come from the landing
  campaign (same core, same harness options, except the heap-snapshot
  option on its ThingsBoard launch). No new launch of the parent was
  made.
- **ThingsBoard events at the guard.** The parent launch had the
  heap-snapshot option. The prototype launches did not, so the event
  counts at the guard (4.69 M against 4.38-4.42 M) are not comparable.
- **Hash counters.** The P1 and P2 census counters use 64-bit hashes of
  the keys. Collisions can lower the distinct counts a little. The
  census sets used about 50-110 MB of heap in a run that ends in OOM.
- **Host load.** Another user's jobs used 4-8 cores from about 15:00 UTC.
  The second P2' OWASP launch (mean load 10.1) and the third P2'
  Stirling-PDF launch (mean load 8.1, its early runs 15-60% slower) ran
  under this load. Their times are not used for a verdict. Their results
  are used.
- **Shadow time.** The `SHADOW` modes add work. The counter launch times
  are not performance numbers.
- **The prescan hang.** The ThingsBoard counter launch failed in the
  legacy prescan ("Prescan jobs have not joined"). That code has no
  prototype change. It occurred in 1 of 6 ThingsBoard launches.
- **P3 model.** The Lean model takes the cover of a position as a
  parameter. It does not model the trie or the `at`/`below`/`admits`
  rules. The property test and the shadow runs check the production
  form.
- **P2' purity.** The proof assumes that the restriction is a function
  of its key. The argument is a code reading and an adversarial review
  (§3.6). It rests on the equality of the cached and uncached query
  paths, which native also assumes. The `SHADOW` launch checks it on
  Conductor only.

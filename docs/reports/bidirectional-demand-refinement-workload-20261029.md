# Demand refinement: performance and next work

Date: 29 October 2026. Measured runtime: `bb74cef6cf483db167c161020a8a4cca576ca005`.

The selected implementation is committed and passes 2,058 core tests and 445 JVM tests.
All four project runs end on TIMEOUT. None ends on OOM. Conductor completes two more
iterations than the saved 16 GB run. Thingsboard still cannot finish run-2. The run-1
engine target of 60 seconds is met on conductor and Stirling, but not OWASP or thingsboard.

The strict baseline comparison retains all locations for OWASP, conductor and thingsboard.
Stirling still misses three baseline locations. These three losses also occur in the saved
16 GB result. Thingsboard still has 5,075 additional candidate identities, far above the
small-extra-result target. The no-FN and few-extra-result gates are therefore **not met**.

The main new finding is avoidable static-demand work. Thingsboard run-2 performs 603.4 million
owner evaluations. Whole-run Java samples put 47.68% inside call-graph reachability.
The next proposal selects relevant static labels before owner checks and computes immutable
owner visibility once. Other projects have different hot work, described below.

## 1. Implementation and validation

The runtime has three commits:

- `c347ff8bb`: restricted admission, FLOW point tails and canonical summary storage.
- `23d0d7677`: reject impossible fixed C5 branches before owner lookup and expansion.
- `bb74cef6c`: cache owner eligibility within one static demand view.

The first commit contains selected semantic changes. It is not a pure speed change.
C2 uses one-step refinement for ANY demand. Run-2 can answer inherited FLOW STAR demand with STAR;
later runs do not select FLOW STAR demand. Abstract FLOW can have EXACT and MUST point tails.
EXACT keeps the read barrier. Field writes update latent exclusions. Complete pure FLOW
summaries replace EXACT with STAR before storage, publication and native persistence.
NORMAL summaries with nonempty exclusions remain persistent. C5 checks the raw emitter
preimage and containment before conclusion restriction and canonicalization.
RemoveAll clears the whole selected position; `RemoveAll(p.f)` is valid. Partial EXACT-only
and BELOW-only all-mark cleaners are invalid.

P1 and P2 keep the selected answers. A finite P1 fixture changes queued states from 2 to 0.
The owner fixture changes 4 first evaluations to 2, with 2 memo hits. These are deterministic
work checks, not project speedup claims. The semantic reference has 2,049 passing core tests;
the final runtime has 2,058 passing core tests, 445 passing JVM tests and a passing classes build.
The five constructive Lean models have 174 checked theorem declarations and 11 true executable
checks. Their axiom audits use only `propext` and `Quot.sound`, in the stated model scope.

The independent source review found no extra grounding, field, source/sink or stop-policy change.
Run-1 still has no ND executable premise. The original backward ZERO exception remains.
Full implementation evidence is in
[the selected implementation data](data/bidirectional-summary-demand-workload-implementation-20261029.json)
and [this report's embedded data](data/bidirectional-demand-refinement-workload-20261029.json).

## 2. Fixed controls

Run `runProjectAnalyzer` directly through Gradle. Use FULL marks, statics and aliases enabled,
`-Xmx16g`, and field limits `1,1,2,3,...`. OWASP has a 1,000-second IFDS budget. Each real project
has 1,080 seconds. The outer budget is 1,200 seconds. These are the selected controls in the
implementation proposal. No extra analyzer configuration or baseline rerun was used.

The fixed finding baseline is the saved `f945f92c5ae554ff4f5fc7696ee5a269210478bb` legacy-core
result. It used 8g, except thingsboard at 12g. The matched 16g comparison uses saved bidi
runtime `c2bc5e78dfdb13f95bda970c5f4e0c247acbac29`. Do not confuse these two comparisons.
Prelaunch and post-run full-content audits both pass for 25 datasets and four model files.

The harness records continuous JFR data, 30-second CPU profiles at run-1
plus 60 seconds and near the IFDS deadline, and automatic OOM snapshots. A fast run-1 correctly
skips the normal CPU capture. Dedicated run-1 JFR files exist for OWASP, conductor and thingsboard.
Stirling run-1 is read from its continuous recording. Extra bounded CPU captures
cover conductor run-4 and Stirling run-5. No heap snapshot was needed or taken.

## 3. Results and latest iterations

The latest column is reached / complete / accepted forward report.

| Project | Current latest | Saved16g latest | Baseline unique | Current unique | Retained baseline | Missing baseline | Added unique |
|---|---|---|---:|---:|---:|---:|---:|
| OWASP | run-12/run-11/run-11 | run-12/run-11/run-11 | 4,112 | 4,112 | 4,112 | 0 | 0 |
| conductor | run-6/run-5/run-5 | run-4/run-3/run-3 | 7 | 7 | 7 | 0 | 0 |
| thingsboard | run-2/run-1/run-1 | run-2/run-1/run-1 | 14 | 5,089 | 14 | 0 | 5,075 |
| Stirling-PDF | run-6/run-5/run-5 | run-6/run-5/run-5 | 17 | 30 | 14 | 3 | 16 |

Every current output is resource-limited. The comparator keeps its original
`INCOMPLETE_OR_INVALID_INPUT_COMPARISON` assessment: analyses time out, and the legacy baseline
has a different planned heap. Available location preservation is not a converged no-FN proof.

### Iteration times and demand frontiers

Each cell is engine seconds / selected outgoing demand memberships. `TO` has no completed
frontier. Direction and field limit are F1, B1, F2, B3, F4, B5, and so on.

| Iteration | OWASP | conductor | thingsboard | Stirling-PDF |
|---|---:|---:|---:|---:|
| run-1 | 100.367 / 111,374 | 13.844 / 33,087 | 349.927 / 1,927,987 | 12.630 / 26,469 |
| run-2 | 37.213 / 112,217 | 32.077 / 340,816 | 367.234 / — TO | 24.870 / 455,608 |
| run-3 | 34.454 / 85 | 22.253 / 23,177 | — | 5.253 / 52,089 |
| run-4 | 39.639 / 200,801 | 635.366 / 47,475 | — | 14.506 / 13,901 |
| run-5 | 30.369 / 0 | 108.790 / 154,853 | — | 612.328 / 1,304 |
| run-6 | 49.198 / 326,227 | 241.444 / — TO | — | 393.611 / — TO |
| run-7 | 30.422 / 0 | — | — | — |
| run-8 | 86.985 / 770,599 | — | — | — |
| run-9 | 32.681 / 0 | — | — | — |
| run-10 | 294.250 / 2,550,055 | — | — | — |
| run-11 | 38.291 / 0 | — | — | — |
| run-12 | 178.614 / — TO | — | — | — |

These D counts are selected summary memberships. They are not scalar fact counts and are not
the unlogged `demandLayerEdges` stop counter.

### Run-1 and transition cost

Times are seconds. RSS is binary GiB and covers the whole command, including export.

| Project/version | Prescan | Engine | Joined static binding | Barrier | Full run-1 iteration | Peak RSS GiB | Latest |
|---|---:|---:|---:|---:|---:|---:|---|
| OWASP saved16g | 31.788 | 92.064 | 0.102 | 2.126 | 94.300 | 18.15 | run-12/run-11/run-11 |
| OWASP current | 33.057 | 100.367 | 0.093 | 2.167 | 102.634 | 17.76 | run-12/run-11/run-11 |
| conductor saved16g | 24.151 | 14.741 | 0.398 | 0.305 | 15.455 | 17.79 | run-4/run-3/run-3 |
| conductor current | 23.333 | 13.844 | 0.385 | 0.364 | 14.601 | 18.02 | run-6/run-5/run-5 |
| thingsboard saved16g | 142.369 | 351.711 | 229.759 | 7.544 | 589.039 | 18.34 | run-2/run-1/run-1 |
| thingsboard current | 123.822 | 349.927 | 230.023 | 8.239 | 588.212 | 18.63 | run-2/run-1/run-1 |
| Stirling-PDF saved16g | 14.466 | 12.758 | 0.155 | 0.214 | 13.131 | 17.83 | run-6/run-5/run-5 |
| Stirling-PDF current | 14.579 | 12.630 | 0.153 | 0.255 | 13.043 | 17.81 | run-6/run-5/run-5 |

Engine time excludes joined static completion. Thingsboard needs 588.212 seconds through its
first barrier: 349.927 engine, 230.023 joined completion and 8.239 barrier, plus small framework
overhead. The later virtual static lookup is paid in run-2, not in this barrier timer.

Conductor run-2 falls from 42.372 to 32.077 seconds, and run-3 from 38.928 to 22.253 seconds.
It now completes run-4 and run-5; the saved run times out in run-4. This is a gain in completed work.
Stirling run-5 falls from 682.927 to 612.328 seconds. Its selected demand frontier falls from
200,779 to 1,304, a 99.35% reduction. It still reaches the same run-6. Thingsboard run-1 and joined
completion are nearly unchanged. OWASP reaches the same run-12. Its run-1 is 100.367 seconds,
versus 92.064 in the saved run. These are single observations, not timing distributions.
A longer interrupted prefix is not a slower completion time.

All fixed legacy-baseline commands completed successfully, in about 123.2, 92.2, 220.4 and 55.1
seconds for OWASP, conductor, thingsboard and Stirling. Current total completion is worse on
all four. The legacy full scan is not a bidi run-1; this comparison does not isolate the effect
of the three selected commits. Exact matched iteration data are embedded in the report JSON.

## 4. Finding locations

Strict identity keeps the rule, sink fingerprint and complete method signature. Do not merge
overloads or replace a return with another return in the same method. Current occurrences are
9,179 OWASP, 7 conductor, 92,016 thingsboard and 77 Stirling. OWASP's 5,067 extra occurrences repeat
retained identities; they add no new unique sink.

### Three Stirling baseline losses, accepted run-5

| Required baseline location | Current observation | Identified mechanism |
|---|---|---|
| `ProcessExecutor.runCommandWithOutputHandling(List, File)`, IR 8, `ProcessBuilder(command)`, line 183 | No same-rule location in that full overload | Existing D23 source-output reset can remove the accumulated command-list mark |
| `ConvertEmlToPDF.convertEmlToPdf(EmlToPdfRequest)`, return IR 103, lines 133–134 | Different return: IR 126, lines 148–149, constant error | Simple exit output selects the last return without a witnessed return instruction |
| `PipelineController.handleData(HandleDataRequest)`, return IR 50, lines 90–91 | Different return: IR 109, line 130, `return null` | Same last-return export fallback |

The command path contains this local loss mechanism:

```java
command.add(request.getUrlInput()); // Generated source gives the receiver ARGS.
command.add("--pdf-forms");          // A false source guard can still cross its receiver reset.
command.add(tempOutputFile.toString());
executor.runCommandWithOutputHandling(command);
```

D23 installs a returned-target reset when the source condition is not statically false.
A later constant append can fail the source branch, while its ordinary result still crosses
that reset. The old ARGS mark can disappear without a replacement; the reverse reset can also
cut its demand. This is a concrete loss mechanism on the baseline path. There is no current
first-loss ledger that proves it is the only loss in this campaign.

The two alternate returns remain strict missing locations. The export fallback explains their
displayed location; it does not prove that the earlier taint path survives. Seven relevant
function bodies or selected arms, five rule files and four project source files are source-bound
in the embedded data. The relevant code is unchanged from the saved 16g runtime. The selected
RemoveAll arm changes elsewhere are excluded from that equality claim. These issues need an
explicit follow-up design; they were not changed to pass this optimization's comparison.

### Additional candidates

Thingsboard adds 5,060 XSS identities and 15 others: six path traversal, three SQL injection,
two SSRF, two reflection, one script engine and one object mapper. XSS accounts for 91,981
occurrences at new identities. The automaton rules include method-end sinks for any function;
the Spring provider delegates the noncontroller branch. This explains the broad sink family,
but not every first mark derivation. Run-2 never completes, so no later forward report refines
these candidates. Unexpected targets include an XSS candidate in Kafka `NetworkReceive.readFrom`.
This is not evidence of a real HTTP-response vulnerability.

Stirling adds 16 XSS identities. None of these additions is automatically a proved FP or a new
vulnerability. All current output uses Simple witnesses without detailed source paths.
Source-witness equality with the baseline cannot be checked from this output.

Against saved16g, conductor removes two `ScriptEvaluator` Graal evaluation candidates and the
reflection candidate in `AnnotatedWorkflowSystemTask.execute`. Stirling removes the added
`AdminLicenseController.uploadLicenseFile` path candidate at `Files.createDirectories`, line 337.
All four were absent from the required baseline. No new required-baseline location is lost.
This is candidate refinement, not a proof that those four locations were false positives.

## 5. Where the work occurs

Thirty source-bound JFR windows pass with seven fresh reader controls. All lie within the observed
Java-sample envelopes; this is not a proof of continuous sampling. Three very short binding windows
have only 3, 11 and 4 samples and are not used for hotspot claims. A Python timestamp-parser error
in the first read attempt was corrected with nine-digit timestamp controls. The failed evidence
is retained. It did not affect an analyzer run.

Java execution samples cover mutator stacks. Native CPU captures also sample GC workers.
Do not mix their denominators. Inclusive shares overlap. Sampled allocation weight is an estimate
of traffic, not retained bytes or an exact allocation total. A method family can include its callbacks.

### Thingsboard: repeated static-demand query work

Latest reached run-2; complete and accepted run-1. The whole run-2 recording has 104,604 Java samples.
C2 contains 58.24%, static entry search 56.31%, call-graph reachability 47.68%, and C5 17.41%.
Sampled allocation weight is about 2,006.675 GiB. Call-graph reachability contains 50.94% of that
weight, about 1,022.247 GiB. Repeated query-local graph scratch, integer boxing and hash-table
construction are a major allocation source. These are auxiliary query operations, not new facts.

The late 30-second native window has a different mix: static completion 41.66%, C5 30.08%,
C2 13.99%, owner eligibility 11.69% and GC workers 43.48%. Do not apply the late C5 share to the
whole run-2. The whole-window GC pause union is 56.745 seconds.

| Run-2 counter at timeout | Value |
|---|---:|
| Owner first evaluations | 603,417,178 |
| Owner memo hits | 154,086,432 |
| Memo views with an allocated table | 2,536,847 |
| Owner families | 16,414 |
| Cumulative memo byte payload allocated | 41,639,806,658 bytes |
| C5 fixed-filter rejection calls | 412,725,931 |
| C5 popped states | 1,531,587 |
| C5 duplicate-state rejections | 19,812,741 |
| C5 composition attempts | 20,819,778 |

The byte count equals views times families. It is not 41.6 GB of live heap. Memo hits are 20.34%
of family questions. P2 removes repeats inside one view, while a new view repeats the graph work.
The counters describe the interrupted run. Rejections include geometry and image failures,
not only mark mismatch. Do not add them or call them unique rejected states.

Source review finds one direct waste: unfiltered FLOW-only adjacency checks owners of colored
labels before it rejects those labels. Each geometry has at most one FLOW label. Direct selection
removes irrelevant label visits and owner questions. Exact mark indexes can remove more visits.
For the remaining real questions, a frozen SCC owner-family index can replace repeated graph
traversal with a bit lookup. Its fixed bit payload bound is 106,815,368 bytes before overhead.
It preserves the existing reachability relation.

Run-1 has another large auxiliary phase. Joined completion processes 2,351,008 writer keys,
222,495,546 candidate input visits, 28,027,422 matches and 27,925,903 bound output calls.
The whole binding profile places 98.57% of Java samples in binding, 41.65% in matching and
34.39% in summary application. GC pause union is only 3.156 seconds of the 230.023-second phase.
Share input selection across outputs with the same complete owner/original; do not remove the binder.
Immediate static supply and caller-owned demand pairs are different results.

The normal run-1 CPU capture puts 26.38% in immediate subscription replay and only 1.25% in fresh
publication delivery. The standing input store merges facts, but each fresh delta still replays
existing summaries. This supports a separate replay-input batching proposal.

### Conductor: summary delivery and replay

Latest reached run-6; complete and accepted run-5. The whole run-4 JFR window puts 56.72% of Java
samples in delivery and 48.10% in engine summary application. Its middle native window gives
65.24% and 49.64%, with GC workers at 34.44%. The event counter can stay unchanged during one
large delivery callback. Run-4 completes, so that observed pause was not an infinite run-4 loop.

The method queue-empty publication barrier already exists. It still delivers separate fresh
publication values. Unlike the old core's merged delta tree, one event envelope can contain many
values with the same complete premise/header. Packing those values can remove repeated matches
and caller continuations. The actual per-flush packing ratio is not logged.

The later run-6 whole-window mix changes: native replay contains 24.22% of Java samples and engine
summary application 26.25%. Its late native capture gives native replay 11.44%, delivery 7.60% and GC workers
42.24%. Native leaf selection is a later target, not a demonstrated two-times project gain.

### OWASP: later ZERO-owned tree growth

Latest reached run-12; complete and accepted run-11. Run-1's whole Java window puts 71.31% in the
call pipeline. Its late normal native capture has 35.98% GC worker samples. The 60-second engine
target is not met.

Later backward runs have no nonzero method admission, but still propagate marked data under ZERO:

| Backward run | Nonzero-input methods | ZERO-only methods | ZERO-owned admitted-delta diagnostic | Outgoing D |
|---|---:|---:|---:|---:|
| run-6 | 0 | 12,082 | 2,724,231 | 326,227 |
| run-8 | 0 | 12,082 | 5,994,383 | 770,599 |
| run-10 | 0 | 12,082 | 19,080,719 | 2,550,055 |

These backward runs have empty incoming entry/pair snapshots, no successful C2 intersections
and no C5 candidates. Native records and ZERO-owned sink requirements still do work. ZERO-only
does not mean only the control ZERO fact. The diagnostic counts are admissions, not scalar paths.

Forward runs 5, 7, 9 and 11 export no selected summary demand. The stop counter also sees incoming
demand links and internal/raw demand before selection. Its exact contribution split is not logged.
The selected frontier alone does not justify a stop-policy change.
The original backward ZERO exception is needed for a sink in a helper that throws without a normal
return: its requirement must still reach the caller. Do not remove that exception.

`BenchmarkTest02326.doPost` grows from 658 outgoing demands in run-4 to 2,626 in run-6, 10,498 in
run-8 and 41,986 in run-10. `BenchmarkTest00544.doPost` reaches 20,590 in run-10. The top 20 methods
hold 17.75% of that frontier. The growth is distributed. The source examples contain parameter
name/value loops. Counts are source-bound; the exact expanding field paths are not logged.

The whole run-12 window puts 55.49% of Java samples in protection and 31.62% at the mask-intersection
leaf. The late native window instead shows 52.75% GC workers and 34.64% inside taint admission.
This is local protected-tree work, not repeated C2/C5 method admission. Changed-packet union and
removal of redundant protection validation need separate proofs and measurements.

### Stirling: unchanged routing, then protected-tree work

Latest reached run-6; complete and accepted run-5. Run-5 completes in 612.328 seconds.
Its middle native capture has 33.21% in `emitUnchanged`, 29.71% in successor routing,
27.19% in call detection and 13.09% in unchanged repeat admission. GC workers have 0.98%.
Whole-window GC pause union is 0.899 seconds. This phase is not dominated by ND products or cleaners.
The unchanged path avoids changed transfers, but still visits instructions. A certified neutral
region jump is a conditional algorithmic target; its actual region lengths are not measured.

Run-6 has different work. Whole-window protection is 55.74% of Java samples; mask intersection is
31.27% at the mask-intersection leaf. The late native window has 28.35% inclusive mask
intersection and 40.69% GC worker samples. Store merge paths can intersect a mask twice even when
union already proves containment. A narrow proved-union constructor could remove those walks
without weakening protection. Generic mask validation must remain for narrowing transfers.

## 6. Memory at 16g

No OOM termination, JVM OOM or automatic HPROF is recorded. Thingsboard's high-memory guard clears
soft references and recovers several times. This is different from OOM. There is no current retained
heap census. Allocation profiles identify traffic; they do not identify retained object ownership.

The selected rows below use rounded after-GC logs. Values can still include garbage. Phase clocks
have about two seconds of alignment uncertainty. Committed capacity is not used memory.

| Project | Run | Last after-GC used GiB | Peak after-GC used GiB | Committed range GiB | Heap max GiB | Latest reached / complete / accepted |
|---|---|---:|---:|---|---:|---|
| OWASP | run-1 | 5.07 | 7.76 | 7.71–11.63 | 16 | run-12 / run-11 / run-11 |
| OWASP | run-2 | 8.23 | 8.23 | 11.63–11.63 | 16 | run-12 / run-11 / run-11 |
| OWASP | run-12 | 8.06 | 14.16 | 16.00–16.00 | 16 | run-12 / run-11 / run-11 |
| conductor | run-1 | 5.79 | 13.05 | 13.41–16.00 | 16 | run-6 / run-5 / run-5 |
| conductor | run-2 | 8.04 | 12.65 | 16.00–16.00 | 16 | run-6 / run-5 / run-5 |
| conductor | run-6 | 9.80 | 14.17 | 16.00–16.00 | 16 | run-6 / run-5 / run-5 |
| thingsboard | run-1 | 9.68 | 14.48 | 16.00–16.00 | 16 | run-2 / run-1 / run-1 |
| thingsboard | run-2 | 14.36 | 15.02 | 16.00–16.00 | 16 | run-2 / run-1 / run-1 |
| Stirling-PDF | run-1 | 5.04 | 5.04 | 8.18–8.50 | 16 | run-6 / run-5 / run-5 |
| Stirling-PDF | run-2 | 6.54 | 12.41 | 8.50–16.00 | 16 | run-6 / run-5 / run-5 |
| Stirling-PDF | run-6 | 10.84 | 14.31 | 14.80–16.00 | 16 | run-6 / run-5 / run-5 |

Peak process RSS is 17.76, 18.02, 18.63 and 17.81 GiB for OWASP, conductor, thingsboard and Stirling.
RSS includes nonheap pages and export. It can exceed the 16 GiB heap limit.

The 16g room avoids OOM in this experiment, but does not produce convergence. A finite trace cannot
prove future memory is bounded or unbounded. Thingsboard still has a large run-2 backlog; OWASP's
later selected demand grows. More heap alone is not demonstrated as the solution.

## 7. Next iteration

The [ranked next proposal](../design/bidirectional-demand-refinement-next-iteration-20261029.md)
keeps the next changes separate from this runtime. The first targets are:

1. Select FLOW and compatible static mark rows before owner checks.
2. Compute owner-family reachability once for the frozen snapshot, after measuring the selector stage.
3. Keep proved protection containment through exact-header unions; remove redundant validation walks.
4. Share joined writer input selection across outputs with one complete owner/original.
5. Merge compatible fresh replay inputs and publication values at the existing owner barriers.

Later candidates cover changed method packets, certified neutral instruction chains and selective
native record leaves. Each has current/new examples, ownership, proof and measurement gates.
No project packing ratio or two-times wall-time gain is claimed. The source-confirmed FLOW-only
fixture can remove n irrelevant colored-owner tests while retaining its single FLOW row.

## 8. Evidence and limits

The [embedded JSON](data/bidirectional-demand-refinement-workload-20261029.json) contains exact
iteration/phase/memory values, finding breakdowns and missing locations, source hashes, input audits,
all profile windows and reader receipts. Fifty current/saved iteration rows were checked against INFO
logs. All 30 JFR windows completed. The raw baseline was reused and not changed.

The implementation tests pass. The project completion, no-FN and few-extra-candidate targets do not.
Sources and sink identities from the detailed baseline cannot be equated with current Simple paths.
Rejected-filter reason counts, per-barrier mergeable packet ratios, exact expanding OWASP paths and
a current retained-object layout are not available. These limits are not replaced by shape guesses.

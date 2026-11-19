# C — Real termination stalls in the HEAD runtime (ground truth)

Scope: HEAD `758ad99ff` (production sources == `0438facd2`, the pre-refinement runtime).
Read-only. "VERIFIED" = read in code, a report, or an archived analyzer log. "INFERENCE" = my reading.

Paths are relative to `/drive-testcomp/opentaint-go-rules/opentaint-w3` unless absolute.
`BIDI=core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi`.
Archived native-control logs (same production tree as HEAD):
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/demand-refinement-rule-prototypes-20261118.n00xyl/baseline/projects/{OWASP,conductor,Stirling-PDF}/bidi/analyzer.log`.

---

## 1. What the current runtime does

### 1.1 Driver and stop test (VERIFIED)

- `BIDI/driver/IterationDriver.kt:29` `class IterationDriver`. "Runs fresh engines in sequence" (line 28): every run is a new `RunManager` (lines 250-252). Nothing of a run's fact/edge state survives except what the barrier persists.
- Loop: `analyze()` lines 44-74; one run = `runOnce()` 77-183; the barrier = `barrier()` 200-235.
- Barrier order (200-235): `report.prepare` (214) → `shared.records.persist` + `persistScoped` (215-216, NORMAL records only) → `HandOff.of` (217) → frontier log (218-220) → stop decision (221-225) → `normalRuleContributors.publish` (229-232, forward only) → `report.commit` (233).
- **The whole stopping test is three lines (221-225):**
  ```kotlin
  forward && handOff.demandEdges.isEmpty() -> End(COMPLETE, NO_DEMAND_EDGE)
  forward && !policy.continueAfter(config, result, frontiers) -> End(COMPLETE, policy.stopReason(config))
  else -> Next.Run(nextConfig(...))
  ```
  Stops are tested only at forward barriers. A backward barrier always continues. `frontiers` (the history of per-run counts) is passed to the policy but no policy reads it.
- Any non-COMPLETE run ends the analysis with the last committed report (line 170); OOM at the barrier likewise (174-182).

### 1.2 Policies, field limits, hard cutoff (VERIFIED)

- `BIDI/driver/IterationPolicy.kt:10` interface; `:24` `HardRunLimitPolicy(delegate, lastForwardRun = 11)`; `continueAfter = run.index < lastForwardRun && delegate…` (34-35); stop reason `RUN_LIMIT` (37-38).
- Production wiring: `configuredIncreasingLimits()` (`IterationPolicy.kt:69-75`) wraps `IncreasingLimits` (55-59, `continueAfter = true`) in the hard limit; used at `core/src/main/kotlin/org/opentaint/jvm/sast/project/JirProjectAnalyzer.kt:64` and `TestProjectAnalyzer.kt:229`.
- Field limit schedule `REPEAT_RUN1`: `maxOf(1, runIndex-1)` (`IterationPolicy.kt:42-52`) → limits `1,1,2,3,…,10` for runs 1..11. Monotone check at `IterationDriver.kt:240`.
- There is no per-run time budget: `timeout(run, remaining) = remaining` (`IterationPolicy.kt:20`). One slow run eats the whole budget.
- End reasons: `STOP_RULE, NO_DEMAND_EDGE, POLICY, RUN_LIMIT, ABNORMAL` (`BIDI/driver/Report.kt:8`). `STOP_RULE` is unused in HEAD (it was used by the prototypes).
- Report at the cutoff: confirmed set C is accumulated over forward barriers (`Report.kt:35-44`, root actors with `ZERO → NormalTarget`); "latest reached" set L is replaced at each forward barrier (61-66); **only `RUN_LIMIT` adds L∖C as provisional** (`Report.kt:70-75`). A natural stop or an abnormal stop reports C only. Spec: `spec/bidirectional-run11-cutoff.md`.
- `spec/retain-demand-at-hard-cutoff.md` is not a runtime mechanism. It is a proof predicate from the redundant-demand campaign: at the final forward barrier any outgoing demand may be dropped as long as one row is kept (the map stays non-empty, so the result is still `RUN_LIMIT` with the same report). It gives no verdict before run-11.

### 1.3 Handoff: how demand is built, stored, and "renewed" (VERIFIED)

- `BIDI/driver/HandOff.kt:26` `class HandOff(demand: DemandStore, seeds: SeedIndex, demandEdges: Map<MethodKey,Int>)`; `HandOff.of` at `:31`.
- Run-1 → run-2: `toBackward` (`HandOff.kt:115`), with the frozen run-1 static completion and "shared static carry". Backward → forward in non-FULL: `toForward` (`:196`). **Every FULL handoff after run-1 uses `toCompacted` (`:44-89`).**
- What counts as demand: `selectedForHandoff` (`BIDI/ap/Demand.kt:136-140`):
  ```kotlin
  if (layer == Layer.DEMAND) return true
  val single = premise as? InitialAp ?: return true          // every ND (multi-premise) summary, any layer
  return direction == Direction.BACKWARD && single.isZero    // backward ZERO→x NORMAL summaries
  ```
  plus every outgoing `DemandTarget` row (`HandOff.kt:56-57, 67-71`) and the same for inner loop blocks (58-66).
- Projection: one `(Dc, Dp)` `PairedDemand` per (result leaf × premise member): `projectSummaryGuidance` (`BIDI/driver/HandoffCompactor.kt:111-125`); Targets: `projectTargetGuidance` (`:127-131`).
- Compaction: `HandoffCompactor.select` (`HandoffCompactor.kt:40-107`) drops an origin only when every one of its rows has another origin with the same exact C2 key and C5 key in the same owner. It is a within-handoff dedupe. Log line `BIDI_HANDOFF_COMPACTION` (`HandOff.kt:83-85`).
- Store: `BIDI/store/DemandStore.kt:10`. A **new** `DemandStore.Builder` is created at every barrier (`HandOff.kt:75`). The next `RunConfig` receives only this store, the seeds, the NORMAL record view and the NORMAL target view (`IterationDriver.kt:237-243`, `BIDI/engine/RunConfig.kt:15-26`).
- **Consequence (the central structural fact): there is no cross-run memory of demand.** Demand is not "kept and renewed"; it is recomputed from scratch from the summary stores of the run that just ended. Nothing records that a `(owner, Dc, Dp)` pair was already issued, answered, or attempted at a smaller limit. Persistent across runs are only: NORMAL records (`BIDI/store/RecordStore.kt:110-112, 239-267`, "a native record must be normal"), confirmed reports and NORMAL targets (`Report.kt:22-69`), NORMAL rule contributors, seeds (rebuilt each handoff).
- In-run consumers of the demand: C2 = `DemandStore.initials` (`DemandStore.kt:131`, per offered actual, "entry-only index"); C5 = `DemandStore.intersect` (`:202`, per newly inferred summary, "selects complete paired rows"); Target admission = `acceptsTarget` (`:321`). The relative cap is `budget = if (depth >= global) global else depth + 1` (`DemandStore.kt:281`). The global cut is `limitFacts` (`BIDI/ap/Limit.kt:7-19`): the cut part is re-emitted on `Layer.DEMAND`.
- How a pair re-creates itself (VERIFIED from the OWASP helper trace, performance report lines 579-601): demand `(Dc→Dp)` admits a start (C2); the body derives a precise raw relation; C5 cuts the output to `FL(Dp)+1`; the cut part is a DEMAND-layer summary; `selectedForHandoff` projects it as the next `(Dc',Dp')`; the opposite run does the mirror step and returns the original pair. The cap is relative to `Dp`, so a larger global limit K changes nothing ("Increasing the global limit beyond those caps leaves the cuts unchanged", perf report 616-617).

### 1.4 Frontier diagnostics (VERIFIED)

`BIDI/driver/Frontier.kt:15` `class Frontier`; `frontierOf` `:37`; log format `:69-78` ("Run N (DIR) frontier: analysed …, demand edges … in … method keys, …, target demand …, reports …, seeds …"). `DemandCause { FIELD_LIMIT_CUT, MAY_TARGET, CLEANER_ROW, MUST_RECORD, DEMAND_INPUT }` exists (`:12`) but `demandByCause` is never filled (`frontierOf` passes no value) — **the runtime does not classify residual demand by cause.** It also does not log the number of *new* NORMAL records per barrier.

---

## 2. Per-project table (native runtime == HEAD)

All four projects use the run-11 cutoff, FULL marks, limits `1,1,2,…,10`.
Sources: `docs/reports/bidirectional-demand-refinement-rule-prototypes-20261118.md:42-47` (fresh native control), `docs/reports/bidirectional-useful-rule-cost-fixes-20261119.md:451-457` (native repeat), `docs/reports/bidirectional-work-reduction-performance-20261112.md:12-17, 155-198` (earlier campaign on the same core tree), and the archived native-control `analyzer.log` files (frontier lines, read directly).

| Project | Stop / runs reached·completed·accepted | Wall s (native samples) | Findings | Reports first reach final value at | Residual demand at last completed barrier | Trend of residual demand |
| --- | --- | --- | --- | --- | --- | --- |
| OWASP | `RUN_LIMIT` / 11·11·11 | 266.0, 225.1, 225.7 (driver 160.4) | 2,633 confirmed, 0 provisional, 0 missing/0 extra vs legacy | **run-3** (2,120 at run-1/2; 2,633 from run-3 to run-11) | H11: 1,111 rows in 460 method keys; Target demand 1,679 (965 method + 714 block rows) | **Exact period-2 in counts from run-7**: H7=H9=H11 (origins 1,752, kept 1,070, rows 1,111, Targets 965/714); H8=H10 (origins 2,074, rows 2,223, Targets 438) |
| Conductor | `TIMEOUT` in run-8 / 8·7·7 | 1,128.7, 1,126.5 (budget 1,080) | 7 confirmed (= all 7 of the partial legacy baseline) | **run-5** (2, 2, 5, 5, 7, 7, 7) | H7: 85,402 rows in 170 method keys; Target demand 4,492 | **Diverging**: forward H3/H5/H7 = 17,468 / 25,114 / 85,402; backward H4/H6 = 29,951 / 149,630. Method keys shrink 329→174→170 while rows per key explode |
| Stirling-PDF | `TIMEOUT` in run-11 / 11·10·9 (sometimes 11·11·11 at ~150 s) | 1,149.3, 1,108.9, 1,109.5 | 32 confirmed (legacy 24; 8 missing/16 extra by exact location, 7 of the 8 are other-return renderings); fast executions add 2 provisional at run-11 | **run-5** (7, 7, 28, 28, 32, then 32 through run-10) | H10: 1,127 rows in 70 keys, Target 39; H9: 892 rows in 70 keys, Target 178 | **Slowly decaying, not periodic**: forward 1,594 / 1,232 / 980 / 892; backward 4,844 / 1,327 / 1,132 / 1,127; keys 440→116→79→70 |
| ThingsBoard | memory guard in run-1 / 1·none·none | 611.6, 360.8, 334.3 | none accepted (legacy 15) | — | no handoff ever | Not a termination problem |

Per-run engine seconds (archived native control log):

| Run | OWASP | Conductor | Stirling-PDF |
| --- | ---: | ---: | ---: |
| 1 F | 79.0 | 21.0 | 41.2 |
| 2 B | 25.5 | 45.7 | 39.5 |
| 3 F | 11.5 | 9.0 | 15.9 |
| 4 B | 3.9 | 134.8 | 9.9 |
| 5 F | 3.8 | 9.4 | 3.6 |
| 6 B | 6.0 | 499.2 | 18.3 |
| 7 F | 3.3 | 122.7 | 33.1 |
| 8 B | 3.6 | 192.5 (timeout) | 32.6 |
| 9 F | 3.3 | — | 725.2 |
| 10 B | 6.7 | — | 19.3 |
| 11 F | 3.5 | — | 70.1 (timeout) |

Time spent after the last change of the report set (from the same log; my arithmetic):
- OWASP: runs 4-11 ≈ 34 s engine of 160 s driver (≈ 21 %).
- Conductor: runs 6-8 ≈ 814 s of ≈ 1,052 s (≈ 77 %); everything through run-5 took ≈ 235 s.
- Stirling-PDF: runs 6-11 ≈ 899 s of ≈ 1,009 s (≈ 89 %); everything through run-5 took ≈ 110 s.

### 2.1 Kind of the residual demand

No report gives a full per-project breakdown by kind (and the runtime does not log one, §1.4). What is established:

**OWASP (VERIFIED, perf report 528-601, 671-684; baseline report 59-110; prototype report 347-363).**
- Target rows dominate the forward frontier: Target demand 1,679 vs 1,111 handoff rows (not additive; one ND origin projects several rows).
- The measured cycle is **FLOW DATA copy obligations regenerated after C5 cuts** in 12 loop-free `doSomething` helpers (6 endpoint patterns each = 72 repeated forward FLOW pairs; shape `arg(1).bytes.[].* → ret.bytes.[any]`, DEMAND), plus caller-side **control/Target rows** (`ZERO → DemandTarget`, `DATA → ZERO`) that those pairs keep alive. On the selected entry: 6 helper DATA + 11 caller control pairs forward, 8 + 22 backward, identical keys from run-7/8 through run-101.
- A second producer is an "inside read" that creates intrinsic MAY before C5.
- Two nested-loop owners (`BenchmarkTest02326#doPost`, `BenchmarkTest01474#doPost`) hold Target → DATA pairs; in the *revised* (rolled back) build these still deepened by one field per pair of runs (20 new pairs at H11). In the native log the counts are flat from run-7.
- Removing only the six helper FLOW pairs at H7 (allow-list ablation) gives a natural `NO_DEMAND_EDGE` at run-11 with identical SARIF identities (baseline report 76-96). So the Target/control rows in this entry are *secondary*: they drain once the copy pairs stop.

**Conductor (VERIFIED from the archived log; kind partly INFERENCE).**
- 88 % of H7 rows are in three owner keys: `ParametersUtils#replace(Map,DocumentContext,String)` ×2 contexts (37,520 + 28,587) and `ParametersUtils#replaceList` (9,193); with `WorkflowExecutorOps#decide` (3,332) the top-5 share is 93 %. At H6 the same two `replace` contexts hold 128,472 of 149,630 rows.
- `replace` ↔ `replaceList` are mutually and self recursive over nested `Map`/`List` values, each inside a `for` loop (`../opentaint-test/opentaint-test-conductor/repo/core/src/main/java/com/netflix/conductor/core/utils/ParametersUtils.java:187-226`).
- Outgoing census (run-7): `flowOutputAnnotations=61,776` vs `concreteOutputMemberships=26,736`; run-6: 134,983 vs 18,286. So the growth is mostly FLOW DATA.
- A decoded run-6 example (Nov-12 report 330-336) has a raw path `arg(2).HeaderIterator.headers.MutablePair.right.MapValue.MapValue.ImmutablePair.right.*` against demand `ret.[any] → arg(0).MapKey.[any]`.
- INFERENCE: this is **loop/recursion demand**: each larger K admits one more container level (`MapValue.MapValue…`), so each run issues genuinely *new, deeper* keys. It is not the same set re-issued. This is the LOOP/REC class the spec explicitly postpones (R39/R40).

**Stirling-PDF (VERIFIED).**
- Residual demand is small (≈ 900-1,100 rows) and concentrated in loop owners: `EmlProcessingUtils#decodeMimeHeader(String)` (two contexts; 190-352 rows), `PipelineProcessor#runPipelineAgainstFiles`, `PdfAttachmentHandler#processInlineImages`, Spring dispatchers.
- The cost is not the frontier. `decodeMimeHeader` with 65 live input groups and 7,107 body packets performs 1.3 M scalar restrictions, 2.6 M full observations and selects 24 M saved records in run-9 (Nov-12 report 362-366). 99.9 % of output budgets are 1 or 2 regardless of K.
- **The same binary is wildly non-deterministic** on this owner: run-9 engine 725.2 s / 390.7 s / 4.45 s, loop-boundary offers 6,389,744 / 4,375,223 / 38,074 (prototype report 175-182; cost-fix report 828-835). In the fast shape run-11 completes in ≈ 150 s total with `RUN_LIMIT`, 32 confirmed + 2 provisional.

**Rule test suite (VERIFIED, Nov-12 report 80-85; perf report 709-759).** 583 of 585 Java cases stop naturally (449 at run-1, 128 at run-3, 3 at run-5, 2 at run-7, 1 at run-9). Two hit the cutoff: `UnsafeFileUploadServlet#doPost` (LOOP Target renewal: the same 30 Target-entry pairs at H5/H7/H9/H11, 44 control pairs at H6/H8/H10; one confirmed report) and `PassthroughFileModelSamples#fileToStringUnsafe` (straight-line; confirmed at run-1, anonymous Target every later forward run).

**Synthetic baselines to run-101** (baseline report 21-48): every acyclic fixture retains exactly 1 Target with 2-7 handoff pairs; recursion fixtures either `RUN_LIMIT` at 101 or time out at run-21/22.

---

## 3. When do reports stop changing vs when does demand stop?

### 3.1 Measurements (VERIFIED)

| Project | Reports final at | Demand empty at | Runs after the last report change, and what they added |
| --- | --- | --- | --- |
| OWASP | run-3 | never (period-2 from run-7) | runs 4-11: 0 confirmed, 0 provisional |
| Conductor | run-5 | never (growing) | runs 6-7 (+ partial 8): 0 confirmed |
| Stirling-PDF | run-5 | never (decaying slowly) | runs 6-10: 0 confirmed; a completed run-11 adds 0 confirmed, 2 provisional |
| OWASP selected entry, run-101 | 2 confirmed, constant | never | 0 new through run-101; 0 provisional |
| file-upload rule test | 1 confirmed by run-5 | never | "151 saved NORMAL DATA rows and 25 saved NORMAL Target rows are stable from run-5" (perf report 730-733) |

In every project each forward run up to the stabilisation point added reports (run-1, run-3, run-5), and no later forward run added one inside the observed window. There is no observed case of "quiet forward run, then a later gain".

### 3.2 Is the residual demand productive?

- **OWASP: pure churn, measured.** The helper ablation gives the same SARIF with a natural stop (baseline report 76-96). On the selected entry the full sealed state (ordered demand, seeds, saved-record index order, condition contributors, retained NORMAL targets, confirmed and latest-reached identities) at H11 equals H9; from run-10 on there are zero global cuts, zero entry-depth rejections and zero paired caps bound by K (cost-fix report 245-254). The event queue sequence and payloads repeat through run-101 (264-268).
- **Conductor: unproductive for reports in the observed window, but not a cycle.** Reports are flat after run-5 while demand grows 3.4× (forward) and 5× (backward) per pair of runs. Whether deeper runs would ever confirm one of the 5 legacy findings is moot (all 7 legacy findings are already present; legacy itself was an OOM-partial run).
- **Stirling-PDF: unproductive for confirmed reports.** Runs 6-11 add only 2 provisional locations.
- **NOT MEASURED on full projects:** the per-barrier count of *new* NORMAL records / NORMAL targets. `record crossings` in the frontier line counts uses, not additions. This is the one missing number that would turn "reports are flat" into "the persistent state is flat". It is cheap to add (`RecordStore.persist` already knows whether a record is new).

### 3.3 The run-level R41 candidates (spec §7.1) and how they were measured

Both change only the driver's stop test at a completed forward seal; C2/C5/publication are untouched.

**(i) "Complete set of retained reports" / observer census** (spec lines 1171-1217; `spec/lean/proposals/termination-rollback-20261118/ObserverCensus.lean`). Stop when every observer (sink) identity that can exist in the closed compiled call closure already has a root NORMAL receipt.
- Measured: stops synthetic global-cut at run-3, root-MAY at run-5, nested-replay and overwrite fixtures at run-5 in 52/51 closure visits; 29 visits in the streaming variant (cost-fix report 302-319).
- **Fails on the real entry**: the compiled OWASP entry has 117 observer keys in 21 contexts / 360 instructions and only 2 confirmed; 115 remain unconfirmed even after evaluating rule conditions over the producible mark set (cost-fix 237-242). So it cannot fire there.

**(ii) "Closed pair of native runs" / repeated state** (spec lines 1219-1319; `ClosedRunPair.lean`, `RecordIndexSeal.lean`). Stop when the sealed state S equals the state two runs ago, a complete witness of `S → B → S` exists, every limit-dependent read in the witness is stable for all higher K, and every latest-reached identity has a NORMAL receipt.
- `ClosedRunPair.lean`: `closedPairRepeats` (induction: any future schedule above the two minima returns to S) and `closedPairPreservesReport` (final confirmed ∪ reached = confirmed at S). It also carries a counterexample: "Equal projected demand can conceal a newly enabled native action" — equality of demand counts/keys alone is insufficient; the transition itself must be limit-independent.
- `RecordIndexSeal.lean`: equality of the saved-record view by ordered-prefix generation counters instead of copying.
- Measured on the selected OWASP entry: first qualifying pair is run-10/run-11 (demand keys already match at H7/H9 but the saved-record basis still differed); the diagnostic stops naturally at run-11 with both reports; driver 2.138 s vs 7.608 s to run-101 (cost-fix 256-268, 330-357). State compared: 17 demand rows (27 field words per side), 1 seed, 98 contributor rows, 22 NORMAL Target rows.
- **Scope of the prototype**: ≤ 4 roots, ≤ 64 joined actors, ≤ 8 actors in the pair verifier, ≤ 64 demand rows, one effective runner (spec 1284-1289). Full projects have 8,401 / 7,210 / 3,719 / 30,791 roots, so **the guard was ineligible on all four project scans**; they matched native endpoints exactly (cost-fix 677-769). It has never been exercised at project scale.
- The pair stop and local copy retirement have different completion points: retiring only the six copy rows at H11 with the same check stops at run-15 (cost-fix 270-274).

---

## 4. Cheapest mechanism the evidence supports

The four projects have four different problems. No single termination rule covers them.

| Project | Real problem | Would a demand-termination rule help? |
| --- | --- | --- |
| OWASP | Benign period-2 cycle of ≈ 1.1k/2.2k rows; 3-6 s per run | Yes, but the prize is ≈ 20-35 s of ≈ 225 s, and a clean `NO_DEMAND_EDGE` instead of `RUN_LIMIT` |
| Conductor | Demand volume diverges with K in a recursive container walker; backward runs cost 46 → 135 → 499 s | Only a rule that stops *without* waiting for a fixed point, or one that widens recursion |
| Stirling-PDF | One loop owner's observation work explodes (and is non-deterministic); frontier is ≈ 1k rows | No. It is a work/ordering pathology inside a run |
| ThingsBoard | Run-1 heap | No |

### (a) Run-level fixed point (state of run i+2 == run i → stop)

- For: OWASP counts are exactly periodic from H7 (log). On the selected entry the full state is proved equal at H9/H11 and the stop reproduces both reports (cost-fix 256-268). Cost is once per forward handoff: compare O(|demand rows|) keys plus generation counters; 54 field-word reads in the measured case.
- Against: (1) Conductor never reaches a fixed point (rows grow); Stirling's counts still drift at H9/H10. It fires on 1 of 3 projects. (2) The existing prototype is whole-scan and bounded to ≤ 4 roots; on real scans it never ran. A useful version must be **per component** (per root or per method-key cluster), which the prototype did not attempt. (3) Sound only with the limit-independence side condition (`ClosedRunPair.lean` counterexample); the cheap check for that is "no global cut, no depth rejection, no K-bound paired cap in the two witness runs", which the runtime can count where it already compares depths. (4) Handoff row counts differ between identical launches (OWASP H11 = 1,017 / 1,111 / 1,153 / 975 across native samples), so the comparison must be on a canonical key set, not on order or count.
- Soundness risk vs pinned baseline: low if the K-independence counters and "L ⊆ C" (no provisional would be exposed) are required; then the report equals the run-11 report by the Lean induction. Without K-independence it is a heuristic.

### (b) Monotone demand (never re-issue a demand already answered at the same or larger limit)

- For: this is exactly what the real OWASP cycle is. The six/eight helper pairs are key-identical from run-7 to run-101, their caps are `FL(Dp)+1 = 1 or 2`, and raising K "leaves both producers active" (baseline report 61-72). Removing them once at H7 ends the scan at run-11 with identical SARIF. The geometry ablation (remove a FLOW pair whose transfer is already replayable from saved NORMAL) over 144 native acyclic cases changed 58 frontiers, gave 36 new natural stops and lost no confirmed observation (cost-fix 130-137).
- Against: (1) HEAD has nowhere to keep it — demand is rebuilt from zero at each barrier (§1.3). It needs a new persistent key set; Conductor's H2 alone has 478k rows, so it must be compact and scoped to post-run-2 handoffs. (2) "Already answered" is the hard part. Dropping a pair also drops the coarse DEMAND replies its callee produced; three such `ret.MAY/T,D` replies at run-5 were needed by a caller continuation (cost-fix 139-190): restoring them once → natural stop at run-9; restoring them always → run-101 again. So a naive "same key seen before → drop" changes which caller-side DEMAND witnesses exist. It kept both confirmed reports in every experiment, but provisional/DEMAND-only reachability can differ. (3) It does nothing for Conductor: there each run issues new, deeper keys (INFERENCE from growth 7,367 → 37,520 rows in one owner). A "same-or-deeper key subsumed by an earlier shallower answer" variant is widening on recursion — the postponed LOOP/REC problem.
- Cost: one hash lookup per projected row at the handoff (O(rows)); nothing per edge.
- Soundness risk: medium. The safe formulation is "a pair re-issued with the same key, whose previous answer involved no K-bound cut, produces the same answer" — that is (a) restricted to one owner. It then needs the owner's inputs (saved records it reads, incoming actuals) to be unchanged too, which is the per-component fixed point again.

### (c) Handoff-time retirement (R41 local / R37-R38 / R42)

- For: R41 geometry stops the OWASP entry at run-7 and two synthetic cases at run-5/7.
- Against, at project scale (prototype report 151-166, 194-198, 222-223; cost-fix 584-616): the sound (closed-root / caller-checked) R41 made **zero attempts** on all four projects; the unsound-as-specified geometry-only variant removed 7/8/5 origins at OWASP H4-H6 (H11 1,111 → 1,002, still `RUN_LIMIT`) and 71 at Conductor H2, then 128 attempts per handoff all returned "unsupported compiled form". R42: "USELESS" (frontier 6 → 3, Target remains, zero new stops). R37/R38: "USELESS" in the copy-only scope. No project changed its reached/completed run under any of them.
- Cost: per-origin proof at the handoff (30-140 visits on toy scopes; 1,255-1,753 counted steps on the one real helper; a 12,000-step quota), plus the unresolved "allowance" accounting of spec §8.2.
- Soundness risk: the continuation proof is open for the only real case it targets (cost-fix 124-128, 511-514).

### (d) What the evidence actually points to

1. **A report-stability stop** (INFERENCE, not prototyped): stop at a forward barrier when the last forward–backward–forward triple added no confirmed report, no new NORMAL record and no new NORMAL target, and L ⊆ C. It is the "closed run pair" with the demand-equality and K-independence conditions replaced by "nothing persistent changed". It is the only candidate that also stops Conductor (after run-7 at the latest, plausibly after run-7 only because run-5 still added reports; it would save the 192 s of run-8 but not the 499 s of run-6) and Stirling (after run-7 or run-9). Cost: three counters at the barrier. Risk: it is a heuristic; a deeper K can in principle confirm something after a quiet triple. Relative to the pinned baseline it can lose (i) confirmed reports first found at runs 9/11 — none observed in the three projects; one rule test reaches run-9 naturally and should be checked — and (ii) the provisional set L∖C, unless the stop is reported with `RUN_LIMIT`-style provisional output. **The missing measurement (new NORMAL records per barrier) decides whether this is viable; add that log first.**
2. **Per-run time budget.** With `timeout = remaining` one backward run (Conductor run-6: 499 s; Stirling run-9: 725 s) consumes the budget, and a TIMEOUT discards the run in progress. A per-run cap proportional to earlier runs would let the scan end with the last accepted forward report at a known point. Zero soundness change relative to today's timeout behaviour.
3. **Stirling is a loop-observation work bug**, not demand. The 160× spread between identical launches (4.45 s vs 725 s for run-9) says the work depends on arrival order at `decodeMimeHeader`'s loop boundary. Any termination design should be evaluated with this fixed or held constant, otherwise Stirling results are noise (the R36 / R41 "improvements" to 150 s were this effect, with zero rule activations).
4. **Conductor needs a bound on recursion-driven demand** (e.g. the relative cap applied per recursive owner across runs, or no deepening for an SCC whose reports and NORMAL records are flat). That is a design item, outside R1-R42.

Ranking by cost/benefit on the evidence: per-barrier "new NORMAL records" log (free) → (d1) report-stability stop or (a) per-component fixed point with K-independence counters → (b) only as the owner-local form of (a) → (c) last (highest cost, zero measured project effect).

---

## 5. Invariants a new proposal must not break, and glossary

### 5.1 Invariants (VERIFIED in spec/code unless marked)

- **Schedule.** Run-1 forward at limit 1, run-2 backward at limit 1, then alternate with limits 2,3,… (`IterationPolicy.kt:42-52`); the limit never decreases (`IterationDriver.kt:240`); run-1 must use limit exactly 1 (`:56`).
- **Fresh engine per run; only barrier-committed state persists** (`IterationDriver.kt:28, 213-233`). Persisted records are NORMAL only (`RecordStore.kt:267`). DEMAND-layer results are never persisted and never reversed (task §3).
- **Stop only at a completed forward barrier**; a failed/timeout/OOM run exposes the previous committed report, never a partial one (`IterationDriver.kt:170-182`).
- **Report policy.** Confirmed = root `ZERO → NormalTarget`; confirmation is monotone across runs (`Report.kt:35-44`). Provisional = latest forward reached set minus confirmed, exposed only at `RUN_LIMIT` (`Report.kt:70-75`). A new stop reason must decide explicitly what happens to L∖C.
- **Field limits** (spec `demand-refinement-and-termination.md:308-332`): instruction results, replay results and incoming actuals are cut at the global K; C2 starts at `min(K, FL(Dc)+1)`; fresh C5 DATA output at `min(K, FL(Dp)+1)` for its own pair (code: `DemandStore.kt:281`); "no relative output exception"; saved NORMAL replay is cut at K only. `FL` counts field and array accessors; a static class anchor counts zero.
- **Exact-may**: a cut never invents taint; the cut-off part is represented as a MAY tail at the retained head on the DEMAND layer (`Limit.kt:7-19`), and an `[any]`/MAY premise can only be satisfied by an `[any]`/MAY fact in the caller (task §3). MAY and NE never serve as owned initials or record read premises (spec lines 99-101).
- **Layers**: NORMAL = proved, persistable, reversible, composes NormalTargets; DEMAND = guidance only. Composition is DEMAND if any participant is DEMAND. A NormalTarget composes only on NORMAL links (`RunMethodCallServices.kt:504, 516`).
- **ND (multi-premise) summaries apply as a full AND**; handoff may project arms separately as guidance but the executable premise stays conjunctive (spec lines 123-127); all ND summaries are handed off regardless of layer (`Demand.kt:138`).
- **Typed controls** ZERO / DemandTarget / NormalTarget are outside DATA and have no AP cap; a retained DemandTarget counts as demand for the stop test.
- **Run-2 is special**: it reads the frozen run-1 static completion and shared static carry (`HandOff.kt:115-168`). The rollback's worst regression (Conductor run-2 OOM, 41 s → 219 s) came from changing C2 starts on that carry route (perf report 233-243, 376-394). Do not touch run-1/run-2 static views.
- **Acceptance gate** (spec §8.4, lines 1720-1759): per project, preserved confirmed identities and progress, and equal-or-better wall time and peak memory; one reproducible regression on one project fails the variant.
- **Measurement hygiene** (INFERENCE from the data): native control variance is larger than most prototype deltas (Stirling run-9 4-725 s; Conductor peak RSS 9.75-10.24 GiB; OWASP H11 975-1,153 rows). Any claim needs interleaved repeats.

### 5.2 Glossary

- **Run-i / barrier / seal / handoff Hi**: run-i is one forward (odd) or backward (even) analysis with a fresh engine. The *barrier* (also "seal") is the single-threaded step after all workers join: persist NORMAL, prepare reports, build the next demand. *Handoff Hi* is the demand store produced by run-i for run-i+1.
- **K**: the global field limit of the current run.
- **NORMAL / DEMAND layers**: every fact and summary carries a layer. NORMAL = derived without any cut or possible binding ("complete edge" in the task); DEMAND = involved a cut/MAY ("demand edge"); it only guides the next run.
- **Tails**: `$` EXACT point; `*` STAR correlated suffix (same suffix on both ends of a relation); `M`/MAY (`[any]`) any suffix, independent; `NE` non-empty MAY (proposed, not in HEAD); `MUST` uniform region (every point below the head is tainted).
- **FLOW / DATA / TAINT**: DATA = an access-path fact (as opposed to a control fact). FLOW (`/F`) = mark-abstract pass-through relation ("whatever is at p.u arrives at q.v"); TAINT (`/T`) = a concrete taint mark. A "FLOW DATA copy obligation" is a demand pair asking for a pass-through relation of a copying callee.
- **ZERO**: the fact-less control premise (unconditional reachability; sources fire from ZERO).
- **Target**: a sink-reached terminal. **NormalTarget(id)** = sink reached by a NORMAL witness (a report when its premise is ZERO at a root). **DemandTarget (DT)** = anonymous "a sink is reachable under the current abstraction"; it is demand.
- **Demand pair `(Dc, Dp)` / guide / selector**: one row of the demand store for an owner (method or loop block): `Dc` = entry pattern (what may be started at the owner's entry in the next run), `Dp` = paired exit pattern (what output is wanted). A *guide* is such a row seen from the next run; a *selector* is the `Dp` side used to filter outputs.
- **C2**: the admission contract/step at an offer: given an actual fact arriving at an owner and the frozen demand, compute the initial facts to start (`DemandStore.initials`). Contract C2 in `spec/ap.md:1987`.
- **C5**: the publication contract/step: before a newly inferred summary is admitted, intersect it with the paired demand rows and cut each selected output at `FL(Dp)+1` (`DemandStore.intersect`). Contract C5 in `spec/ap.md:1990`. The part cut off is a DEMAND summary — this is where demand is regenerated.
- **Cut**: truncation of a path at a limit (global K = "global cut"; `FL(Dp)+1` = "paired/relative cap"). A **uniform cut guide** is the demand row produced when a definite uniform (MUST) reply is cut below its head (the R42 case).
- **Origin / projection**: an origin is one whole summary or Target row; its projection is the set of `(Dc, Dp)` rows it yields at the handoff.
- **Compaction**: within-handoff removal of an origin whose rows all have another origin with the same C2 and C5 service keys.
- **Saved record / replay / provider**: a persisted NORMAL summary; applying it in a later run is "replay"; a record that can serve a demand is its "provider".
- **Cleaner**: a rule/statement that removes taint (sanitizer, strong overwrite); "point cleaner" removes an exact point, "subtree cleaner" a whole region. Cleaners leave exclusions (`E` for fields, `mx` for marks).
- **Receipt**: a retained root NORMAL witness for one report identity.
- **R41**: retire a FLOW demand whose transfer is independently replayable from saved NORMAL records (local form), or stop at a "certified forward seal" (run-level forms: observer census; closed run pair). **R42**: drop a cut guide already served by a same-lane definite MUST provider. **R37/R38**: retire a root DemandTarget when every possible origin has a NORMAL track or provably no route. **R39/R40**: loop/recursion retirement — postponed.

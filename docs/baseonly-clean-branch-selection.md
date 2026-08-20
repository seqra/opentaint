# Ranking of non-BaseOnly changes by perf impact (conductor / thingsboard)

Baseline = `feb2094fa` (tag `baseline-experiments`). Fork point = `6adc217f2`.
97 commits, 252 files, +35151/-847. Scope here excludes `ap/ifds/access/baseonly/**`.

**Two of the changes ranked Tier 1 below were later removed** — see "Tier 6" and
`e2e-regression-2026-08-19.md`. This document was written before that end-to-end run and the
ranking is left as it was recorded, with the two entries moved out of Tier 1 rather than edited
in place, so the reasoning that promoted them stays visible next to the evidence that demoted
them. The measured-results tables below describe the branch *including* both; the branch no
longer contains either, and no benchmark difference was measurable without them.

Measurement protocol: `-Xmx12g`, quiet machine, alternating configs, N reps, **min** per cell
(interference only adds time, so min is the robust estimator).

---

## Tier 0 — Architecture. Not optional; removing any of it removes the experiment.

| # | Change | Why it is Tier 0 |
|---|---|---|
| 0.1 | `Phase.ShallowScan` + `Phase.FullScan(actionableRules)` payload | the staged contract itself |
| 0.2 | `TaintAnalyzer.analyzeStaged` 3-phase driver + budget split | the pipeline |
| 0.3 | **`SelectedTaintRulesProvider` / `SelectedGoTaintRulesProvider`** — statement-exact rule gating | *the* full-scan cost reduction ("method-level rule search") |
| 0.4 | `TraceActionSearcher` + `resolveVulnerabilityActionableRules` | produces the rule map |
| 0.5 | `selectRules(relevantRuleIds)` moved Prescan→ShallowScan | shallow phase runs on the reduced rule set |
| 0.6 | **`overApproximateMethodContext`** selective context sharing | "better method context management for the shallow scan" |
| 0.7 | Phase-boundary correctness set: `analyzerEnqueued` reset; AP-reset rebuilds summary serializer; non-positive timeout guards; `Cancelled : CancellationException`; per-run `MemoryManager` state | without these the staged pipeline silently drops work or aborts the full scan on its first GC |
| 0.8 | F2F `add` returns a list of changed finals | BaseOnly layered summaries need it; also fixes real dropped-delta bugs in Cactus/Automata |

## Tier 1 — Largest structural wins (keep)

| # | Change | thingsboard | conductor |
|---|---|---|---|
| 1.3 | BaseOnly conclusion-grouped F2F worklist + `createFactToFactTransfer` | HIGH | MED |
| 1.4 | `TraceEdges` conjunctive premises + exact-cube fallback + exclusion normalization | MED | HIGH |
| 1.5 | Boundary quotient: `InterProceduralMethodEntryNode` + field-generalization start-trace memo | MED | HIGH |
| 1.6 | Over-approximate start-trace resolution | MED | HIGH |
| 1.7 | `JTryBoundaryExceptionsApplicationGraph` (also a correctness fix) | HIGH | LOW-MED |

## Tier 2 — Real but smaller; cheap to keep

Rule-storage lock removal; zero-to-zero edge prioritization; skip empty summary-delta
publications; BaseOnly wildcard call-summary domination; `entriesThatCanReach` linear
corridor reachability; ND summary dedup / sequent accumulation / ND activation batching;
side-effect requirement delta tracking; lazy condition rewriter; `mkFalse` singleton;
`trackExternalMethod` early exit; summary-rewriter identity fast path.

## Tier 3 — Correctness fixes worth keeping regardless of perf

`ConcurrentReadSafeObject2IntMap` seqlock; `JIRCallResolver` override-cache key
(`method` → `method+baseClass`); Spring overloaded-controller entry points; bridge-method
argument filtering.

## Tier 6 — Removed after end-to-end measurement

Both were ranked Tier 1 on benchmark time and both were deleted after the 2026-08-19 e2e run
across 28 projects showed them costing recall. Neither removal was measurable on thingsboard or
conductor, which is the whole point: the two benchmarks that promoted them could not see what
they cost. Full evidence in `e2e-regression-2026-08-19.md`.

| # | Change | Why it was removed |
|---|---|---|
| 6.1 | shallow-scan statement collapsing: an analysis-manager predicate for "this statement is provably the identity on this fact", plus the analyzer's transparent-successor walk and its per-(statement, fact) closure memo | Forward-only, with no mirror in the backward resolver. The trace resolver probes for edges at statements the forward pass deliberately never wrote, so resolution fails and the finding is dropped: **11 lost findings**. The mirror was implementable, but with no measurable benefit to protect it there was nothing to weigh against the risk. |
| 6.2 | class-static call skipping: a per-SCC index of the class-static accesses reachable from each call-graph component, a forward skip for calls whose component cannot observe the fact, and the matching backward relevance mirror | Two soundness inversions: an unresolved callee was treated as observing nothing (every Spring `@Autowired` read compiles to an unresolvable stub), and the most general fact — the whole-static-heap access — was judged to observe nothing because the test was containment rather than overlap. **8 lost findings**, plus one compounded with 6.1. Fixing the second inversion re-admits exactly the fact the index existed to prune. |

Their samples and regression tests were kept and now pin the restored recall.

## Tier 7 — Added after the same measurement

| # | Change | Why |
|---|---|---|
| 7.1 | Spring Data custom-fragment override fallback in `JIRCallResolver` | The Tier 3 override-cache re-key is correct, but the old method-only key was the only thing making fragment implementations reachable, by accident. **2 lost findings**, ap-mode independent. Folded into the cache-key commit so the branch never carries the regression. |
| 7.2 | dedicated storage for abstract static edges in `MethodAnalyzerEdges` | Adapted from upstream `cbe3b3ffc`. An edge whose initial and final access are both the depth-0 class-static access carries only an exclusion set; collapsing the family to one exclusion set per statement is where the class-static cost actually goes, without pruning anything. |
| 7.3 | interning of resolved rule objects | Rules resolve per (method, rule) and are retained for the analyzer's lifetime; the exit-sink `anyFunction()` rule matches every method. Retained payload for the duplicated values: 17,295,256 B to 53,520 B over 2000 methods. |

## Tier 4 — Measured for removal (see results section)

| # | Change | Rationale for suspicion |
|---|---|---|
| 4.1 | Forward-fallback family: `ExactProcessingTimeBudget` (10 s/vuln), `HybridActionableRuleSelection`, `ForwardActionableRulesRecorder`, `MethodTaintMarkReachabilityIndex`, `TaintRuleMarkFlow`, `relevantForwardActionableRules` | pays an always-on cost (`taintMarks()` on **every** published summary edge in **every** phase) to make a *fallback* cheaper; the 10 s constant makes results non-deterministic |
| 4.2 | Bolt-on caches: `traceResolverCache`, JVM trace-precondition caches, `baseOnlyNDSearchCache` + `modificationVersion`, `baseOnlyMethodCallSummaryHandlers`, `baseOnlyPrepared{F2F,ND}Summaries`, `cachedRawCallResolution` | unbounded per-analyzer retention; ND cache flushes on *any* edge addition so its hit rate may be ~0 |
| 4.3 | ND `emptyDeltaRequired = true` on the **non-BaseOnly** path | the only pruning in the range that changes **full-scan** semantics; unquantified recall risk |
| 4.4 | `alwaysIgnoreMethod(declaredMethod)` made unconditional | deliberate recall trade: `o.toString()` no longer enters project code |

## Tier 5 — Removed: telemetry and dead scaffolding (no perf benefit, some cost)

- 20+ BaseOnly counters in `MethodAnalyzer` + `BaseOnlyF2FGroupKindStats` in `UnitRunnerStats`
- the statement-collapse diagnostic map, retaining every initial fact per closure key
- `InterProceduralTraceGraphBuilder.debugInfo()` (+8 key types) — `@Synchronized` on the same
  monitor as `process()`, invoked every 10 s for the top-10 active vulnerabilities
- `logger.info` → `logger.debug` for the stats dump, `reportExactTime` (per vuln per stage),
  and the mark-reachability filter line (per vuln)
- `TraceSummarizer` / `TraceMetadata` / `shouldMaterializeNode` — inert: no production call
  site ever passed a summarizer
- dead members: `SelectedRuleSet.methodCleaner` / `callCleaner`, the footprint index's unused
  `reset()` and `Node.context`, `EntryMapper.mapping` visibility, unused `builder` / `origin`
  params, unused `BaseOnlyApManager` import
- sink-only SARIF fingerprint (`vulnerabilitySinkHash/v1`) — added purely for A/B comparison

---

# Measured results

Shared 20-core box. Load average ranged 4-17 during the session, and that turned out to
dominate everything: wall-clock has a roughly +-25% band, and because the phases are
time-boxed, step counts move with load too. Configs were interleaved and the table reports
**min** per cell. `prescan` is the built-in noise gauge — it is identical TreeApManager work in
every config, so any prescan delta between configs that do not touch prescan is pure noise.

## Headline: baseline vs clean branch (quiet machine, interleaved, min of N)

| project | config | prescan | shallow | fwd | actionable | full | TOTAL | findings |
|---|---|--:|--:|--:|--:|--:|--:|--:|
| thingsboard | baseline | 46.8s | 62.4s | 50.2s | 10.2s | 15.3s | **125.2s** | 13 or 14 |
| thingsboard | clean | 47.2s | 60.3s | 47.7s | 10.2s | 15.2s | **123.2s** | 14 |
| conductor | baseline | 12.4s | 17.5s | 9.9s | 7.5s | 2.7s | **33.8s** | 4 |
| conductor | clean | 12.1s | 17.4s | 9.8s | 7.0s | 2.7s | **32.7s** | 4 |

(n=3 per cell.) **Performance-equivalent to slightly better — thingsboard -1.6%, conductor -3.3% — with findings equal or better.** The baseline oscillates between 13 and 14
thingsboard findings across reps (known time-budget non-determinism); the clean branch returned
14 on every rep observed.

## Correction: the telemetry strip is not a speed-up

An earlier pass measured the telemetry strip at -17% thingsboard / -5% conductor. Repeating it
once the machine quietened showed the *baseline* running at 125.2s, i.e. the same as the
stripped build — so that 149.9s baseline figure was load artifact, not signal. The honest claim
for the telemetry removal is **no measurable cost and no measurable benefit at this noise
floor**; it is justified on code-hygiene grounds (and by removing a `@Synchronized` 10-second
graph sweep and an unbounded diagnostic retention map), not on a measured speed-up.

## Ablations — every suspect was retained

Measured while the machine was loaded, so the magnitudes are unreliable; the *sign* was
consistent across both projects for all three, and no ablation recovered a finding.

| project | config | TOTAL | vs stripped | findings |
|---|---|--:|--:|--:|
| thingsboard | stripped | 124.3s | — | 14 |
| thingsboard | minus caches | 159.0s | slower | 14 |
| thingsboard | minus ND empty-delta prune | 153.4s | slower | 14 |
| thingsboard | minus Object-method short-circuit | 150.5s | slower | 14 |
| conductor | stripped | 35.0s | — | 4 |
| conductor | minus caches | 41.4s | slower | 4 |
| conductor | minus ND empty-delta prune | 36.9s | slower | 4 |
| conductor | minus Object-method short-circuit | 41.7s | slower | 4 |

Nothing here refutes the hypothesis that these three pay for themselves, and none of them buys
recall, so all three stay. They are **not** the "irrelevant caches/hacks" — the telemetry was.

# Follow-ups not taken (out of scope for this branch)

1. `TaintAnalysisUnitRunnerManager.newSummaryEdges` populates the taint-mark reachability
   index on **every** published summary edge in **every** phase, allocating two `HashSet`s
   per fact, but the index is only read on the shallow-scan fallback path. Gating it on
   `Phase.ShallowScan` is free work removal; not done here because it could not be measured
   above the noise floor on this machine.
2. `shallowRuleSearchExactTimeLimit = 10.seconds` and the phase budget fractions
   (0.30 / 0.40 / 0.50 / 0.80 / 0.90) are hardcoded and not configurable. The 10 s constant
   makes discovery counts machine-speed dependent.
3. The ND `emptyDeltaRequired = true` prune is the only change in the range that alters
   **full-scan** semantics for the default Tree mode. Both benchmarks are unaffected, but it
   deserves a wider regression run before merging.
4. `TaintMarkManager` was a plain `HashMap` reached from the rule resolvers, which run
   concurrently — fixed here by making it a `ConcurrentHashMap`. The same review found
   `cachedRawCallResolution` being read across unit-runner threads while backed by a plain
   `Int2ObjectOpenHashMap`; that race is pre-existing and still open.

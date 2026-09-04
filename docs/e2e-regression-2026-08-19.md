# e2e regression analysis — `saloed/base-only-clean` vs base

Run of 2026-08-19. New analyzer `e2bd0f883` (the then branch tip, 21 commits) against base
`6adc217f2`, 28 projects. Raw output in `run-debug/`.

**Status.** This analysis is why the branch was rewritten. The two optimisations it convicts —
shallow-scan statement collapsing and class-static call skipping — were removed rather than
repaired, so the history this document analyses no longer exists and the commits it cites by hash
are not on the branch. Sections 1-8 are kept verbatim as the evidence for that decision; section 9
records what was actually done.

**Verdict: the branch is not ready.** 23 findings are genuinely lost (2 more are the accepted
boxed-primitive class and are dismissed), and thingsboard's shallow scan is aborted by the memory
watchdog.

Every loss now has an identified source, and the headline is that **none of them is a precision
limit of field-insensitivity.** Three of the branch's own performance commits prune or skip work in
an unsound direction, and the staged pipeline then converts each of those into a hard false negative
because the full scan can only look where the shallow pass already looked.

---

## 1. How much was actually lost

`run-debug/regression-diff/report.md` reports 12 failing projects. That number is
inflated: the diff keys on the `codeFlows` **count**, so a finding whose flow count
changed at an unchanged location is counted as one removal plus one addition.

Matching instead on `(ruleId, path, startLine, startColumn, endColumn)` and ignoring the
flow count:

| | count |
|---|---:|
| findings genuinely lost | **25** |
| findings genuinely new | 1 (conductor path-format change — not a real gain) |
| findings present in both | 1213 |
| of those, flow count changed | 28 (15 down, 13 **up**) |

WebGoat and maku-boot appear as failures but lost nothing at all.

## 2. Where the 25 died — root causes

Every loss now has an identified source. Counted per rule, not per project: per-project totals
mislead, because shopizer's two lost sql-injection discoveries were masked by two spurious ssrf
discoveries appearing.

| findings | exact source | commit | ap-mode dependent |
|---:|---|---|---|
| **11** | `isTransparentToFact` — forward-only optimisation with no backward mirror | `2e5cf6f40` | BaseOnly-gated |
| **8** | ClassStatic pruning — two soundness inversions | `c7c1b0603` | BaseOnly-gated |
| **2** | override-cache re-key vs Spring Data custom fragments | `86481be76` | **no** |
| **1** | both of the above, compounded (Stirling `LicenseKeyChecker.java:98`) | `c7c1b0603` | BaseOnly-gated |
| 2 | taint on a boxed primitive — **accepted behaviour, dismissed** | — | — |
| 1 | not a loss — class name became a file path (conductor) | — | — |

None of this is resource truncation. Across all eight affected projects there is no timeout, no phase
failure, and no memory-guard event; every shallow scan converged in 0.45–19.6 s against a ~420 s
budget. None of the losses is a budget effect — every `no_trace` outcome converged in 1–351 ms
against a 10 s per-vulnerability limit.

Prescan rule selection is exonerated: the `Select N from 6048 rules` line is identical between base
and new on every project.

**The gates chain.** Within a project these causes are independent but sequential, so fixing one
alone frequently recovers nothing — the finding simply dies at the next gate. Partial fixes will
look like failures. This was measured directly: ablating the ClassStatic prune restored discovery on
one sample but the finding still died at the rule-search `Failed` drop.

## 3. The 11 — a forward pass that never tells the backward pass what it skipped

`JIRAnalysisManager.kt:415-444`, gated at :422 with `if (apManager !is BaseOnlyApManager) return
false`. When a statement cannot touch a fact, `MethodAnalyzer.kt:391` calls
`propagateTransparentFactGroup`, which jumps the fact to the transparent closure's boundary and
**writes no `MethodAnalyzerEdges` entry for the skipped statements**.

The backward trace resolver walks the CFG statement by statement and probes
`MethodTraceResolver.kt:2313 containsEntryEdge`, which finds the storage empty. It returns false not
because any access-path relation disagreed, but because the candidate set is empty before any
comparison happens. From there: `applicableEdges.isEmpty() -> continue`, `actions.isEmpty() ->
return`, `startNodes.isEmpty()`, requests exhausted, `TraceResolver.kt:252 return NoTrace`.

The broadest clause is line 436 — any statement that is not an assign, return or throw (an `if`
branch, a goto) is transparent for **every** fact.

Measured end to end on tms with the local project model, varying only the shallow-scan knob:

| variant | findings | `FileController:433` | `no_trace` | `Failed` |
|---|---:|---|---:|---:|
| BaseOnlyField (shipped) | 152 | missing | 24 | 27 |
| + ClassStatic prune disabled | 152 | missing | 24 | — |
| + alt-premise cube fallback | 152 | missing | 0 | 27 |
| **+ transparent statements disabled** | **153** | **present** | **0** | **0** |
| Tree shallow scan | 153 | present | 0 | 0 |
| base `6adc217f2` | 153 | present | — | — |

Necessary and sufficient. **A bug, not a consequence of field-insensitivity** — no access-path
relation is consulted anywhere in the chain, and `enableTraceResolutionMode()` cannot help because it
cannot re-create omitted edges.

Also found and disproved as the cause: the alternative-premises guard
(`MethodTraceResolver.kt:764-766`). BaseOnly conjoins alternatives into one `SummaryTrace` instead of
Tree's cartesian product, so the guaranteed-non-empty shortcut is skipped. Adding a cube fallback
took `no_trace` 24 -> 0 but the finding stayed lost. It is a genuine defect —
commit `4e8082f4d`'s claim that nothing is lost there is false, since the cube fallback only fires on
`actionHardLimitReached` — but it is not the root cause.

## 4. The 8 — ClassStatic pruning prunes in the wrong direction

Both defects come from `c7c1b0603` and are gated `if (apManager !is BaseOnlyApManager) return true`,
so they never run in Tree. That is why base was unaffected, and why they present as BaseOnly problems
when they are not.

**Defect 1 — an unresolved callee is treated as "cannot observe."** `JIRAnalysisManager.kt:464`:

```kotlin
JIRCallResolver.MethodResolutionResult.MethodResolutionFailed -> Unit
```

The loop returns `false` (relevant) only when it finds a relevant target; an unresolved callee
contributes nothing and the function falls through to `return true` = "definitely irrelevant".
Unknown is read as safe when it must be read as relevant. This is fatal because OpenTaint compiles
every Spring `@Autowired` read into a non-deterministic stub whose `nextBool()` never resolves — so
every ClassStatic fact is transparent at every bean-injection site. The same gate is also blind to
receiver aliasing: a callee reading `this.metadataDao` records zero static accessors, so the call is
pruned even though the caller loaded that receiver from the registry.

**Defect 2 — the most general fact is judged to observe nothing.**
`JIRClassStaticFootprintIndex.factMayObserve` (lines 394-404) reads the footprint path off the fact; for `EMPTY_ACCESS`
(`<static>/{}`) — the whole-static-heap fact that crosses every intermediate frame — `readAccessor`
returns null on the first accessor. It implements "fact contains access" where the correct predicate
is overlap. That is why the failure needs exactly one extra frame: writing then calling `run()`
directly survives, while `runIt(task) -> task.run()` and `Thread.start() -> t.run()` both die.

Measured ablation, showing the two are independently sufficient and that which one binds depends on
call shape:

| ablation | cross-entry-point sample | group-A samples |
|---|---|---|
| tip | discovery **0** | discovery 2 -> `Failed` |
| `mayObserve` off | discovery 1 -> still `Failed` | discovery 2 -> `Failed` |
| unresolved-callee fixed | discovery 0 | **`Collected` -> found** |
| both | **found** | **found** |

`overApproximateMethodContext` is refuted as a cause — measured, no effect.

A separate defect worth its own ticket: the footprint index is a one-shot snapshot of `contexts()`
taken under `getOrBuildIndex()`, so pruning depends on method analysis order and is
non-deterministic.

## 5. The 2 — a correct fix that removed a load-bearing accident

`86481be76` re-keyed `JIRCallResolver.methodOverridesCache` from `JIRMethod` to
`Pair<JIRMethod, JIRClassOrInterface>`. The new key is correct; the problem is that the old, wrong
key was load-bearing.

Shopizer uses the Spring Data custom-fragment pattern:

```java
interface ProductRepository extends JpaRepository<Product,Long>, ProductRepositoryCustom { }
class ProductRepositoryImpl implements ProductRepositoryCustom { }   // NOT a ProductRepository
```

The call receiver at `ProductServiceImpl.java:353` is typed `ProductRepository`, so
`findOverrides(method, baseClass = ProductRepository)` correctly cannot return
`ProductRepositoryImpl`. Base reached it only by cache aliasing across call sites.
`ProductRepositoryCustom` and `ProductRepositoryImpl` are referenced by type nowhere else in
shopizer, so nothing else registers the impl.

This loss is **ap-mode independent** — both `Tree` and `BaseOnlyField` give `raw=0`, and restoring
the old cache key restores the finding in both. Corroborating: shopizer's prescan, which is
TreeApManager in both runs, drops 54,068 -> 45,437 steps, and `ProductRepositoryImpl#listByStore`
goes from `steps 1118 | sum 200` to `steps 521 | sum 0` — it never produces a summary in any phase.
The bridge-argument filter and the unconditional `alwaysIgnoreMethod` were ablated individually and
exonerated.

Do not fix by reverting the cache key — the old behaviour was accidental and order-dependent. Model
the Spring Data fragment relation explicitly instead.

## 6. Stirling `LicenseKeyChecker.java:98` — a true positive found for the wrong reason

The vulnerability is real, and verified in the scanned sources: `saveLicenseKey(@RequestBody
Map<String,String>)` -> `request.get("licenseKey")` -> `updateLicenseKey` ->
`applicationProperties.getPremium().setKey(newKey)` -> `getLicenseKeyContent` -> `substring` ->
`Paths.get` -> `Files.exists` / `Files.readString`, with no sanitization on that path.

But **neither analyzer ever derived that store.** Across all 891 threadFlow steps of the base run,
not one assign/propagate-to target names `ApplicationProperties`, `Premium` or `key`. Base reported
the finding via an over-approximated ClassStatic start plus a spurious parameter-hop prefix — the
right answer for the wrong reason. Restoring it through the rule-selection fix alone would bring it
back with the same bogus trace; deriving it properly needs the `@RequestBody Map` element-propagation
gap fixed, which is a separate issue.

## 7. thingsboard: the OOM

The status is `[complete, high_memory, oom]`, 473 s, exit 253. No `OutOfMemoryError`
appears in any log and the SARIF is complete with 14 findings identical to base.

Exit 253 comes from the soft watchdog: `OOM_DETECTION_THRESHOLD = 0.90`
(`TaintAnalysisUnitRunnerManager.kt:839`) of the 12 GiB cap. Its handler calls
`cancellation.cancel()`, so **the shallow scan was aborted at 13:44:34, not converged** —
14,594 events were still enqueued. Already-found discoveries survive
(`vulnerabilityBuckets` is untouched by `cancel()`), but since the full scan only arms
rules at discovered statements, any corridor the aborted scan never reached is silently
unarmed. It happened to still find all 14; that is luck, not a property.

`updateFailureStatus` is `compareAndSet(OK, status)`, so a preparatory phase's OOM is
sticky and turns a complete, correct run into a reported failure.

### Where the time went

Base is **not** single-phase — it runs prescan + full scan.

| stage | base | new | Δ |
|---|--:|--:|--:|
| load + IR | 69 s | 71 s | +2 |
| prescan | 180 s | 139 s | **−41** |
| shallow scan | — | 210 s | **+210** |
| full scan | 65 s | 40 s | **−25** |
| SARIF | 5 s | 9 s | +4 |
| **total** | **319 s** | **469 s** | **+150** |

The perf commits paid off — prescan −23%, full scan −38%. The entire regression is the new
phase.

### Why the "cheaper" mode costs more: the throttle is dead code

`MethodAnalyzer.kt:774-778` is the engine's only fact-explosion backpressure:

```kotlin
if (edge.initialFactAp.depth > factDepthLimit) return true       // factDepthLimit starts at 3
if (edge.factAp.depth > factDepthLimit + 2) return true          // i.e. > 5
```

`INITIAL_ALLOWED_FACT_DEPTH = 3` (`MethodAnalyzer.kt:1855`). BaseOnly's `depth` is
`BaseOnlyAccess.size`, which counts three optional slots and is therefore 0–3
(`BaseOnlyAccess.kt:148-155`, `BaseOnlyFinalFactAp.kt:27`, `BaseOnlyInitialFactAp.kt:23`).
**Both clauses are unreachable in BaseOnly mode.** `registerDelayed` never fires and no
unit ever escalates its fact limit during the shallow scan.

Measured: 1,293 `Increase unit fact limit` events in the new run — 46 in prescan, 1,198 in
the 40 s full scan, and **zero in 188 s of shallow scan** (its 49 are all stamped at the
second prescan ended). Field-insensitivity shrinks each fact but multiplies distinct facts,
and nothing throttles that: the shallow scan performs 1,738,208 fact-type checks, 2.1× base's
entire full scan. `AccessValidator.validateApiUsageState` went from 514 handled summaries in
base's whole run to 111,516.

Live-set decomposition at the trip (post-GC values only — the `Memory usage:` log lines are
`maxMemory − freeMemory` and include uncollected garbage):

```
 ~5.4 GB  baseline live, also present in base
+~2.3 GB  added by shallow, NOT released at the phase switch
+~3.8 GB  shallow-phase-local, released at the switch
=~11.6 GB  vs an 11.60 GB threshold
```

Live then reached 12.87 GB (99.9%) during actionable-rule trace resolution — about 1.3 GB
added by resolving 23 traces in 20 s.

## 8. codeFlows counts

Only 28 of 1213 surviving findings changed flow count, and 13 of those went **up**. The
governor is not new: `MethodTraceSearch.selectMethodTraces` (`MethodTraceSearch.kt:184-282`)
is a greedy set-cover over *method nodes*, not a path enumerator — line 244 stops as soon as
every method node is covered, even for `(sink, source)` pairs never connected. That file is
byte-identical between base and new; the counts moved only because `4e8082f4d` quotiented
the graph. No hard cap fired.

Where counts fell, the dedup is correct: WebGoat `UserService:53` 6→2 and Stirling
`AdminLicenseController` 8→1 drop only flows that are the identical genuine tail prefixed by
a bogus `Exiting X / Entering Y` hop between handlers that never call each other. Both
genuine paths survive.

Where counts rose, quality regressed: hertzbeat 1→2 *adds* such a spurious prefix, another
hertzbeat finding swaps its representative for a bogus-prefixed one, and tms
`BlogController:1637` loses the genuine flow entirely.

The representative is not deterministic — `generalizedStart2FinalTraceCache`
(`TraceResolver.kt:606-637`) is a `ConcurrentHashMap` with first-writer-wins under parallel
workers.

## 9. What to fix

Recall. These must land **together** — the gates chain, so any one alone recovers little and will
look like a failed fix.

1. **Done — `isTransparentToFact` and its transparent-closure machinery removed.** The backward mirror was the alternative: teach the
   trace resolver to treat a collapsed statement as edge-present and continue to its predecessors.
   It was not taken. Both benchmarks were performance-equivalent without the optimisation, so the
   forward-only pruning was deleted instead of being made two-sided, and the branch no longer
   contains it. Recovers 11.
2. **Done — `JIRClassStaticFootprintIndex` and its call-skipping consumers removed.** Repairing it needed two changes that pull against
   each other: read an unresolved callee as relevant rather than irrelevant, and make the
   observation test an overlap rather than a containment test — the second re-admits exactly the
   whole-static-heap fact the optimisation existed to prune, so the repaired version buys close to
   nothing. The footprint index, the forward skip and its backward mirror were deleted. Recovers 8,
   plus the compounded Stirling finding.
3. **Kept as tests.** The samples and regression tests that came with the skipped-call work are
   retained; they now pin the recall the removal restores.
4. **Route `Failed` into the forward fallback** alongside `Unprocessed`
   (`HybridActionableRuleSelection.kt:12-17`). JVM already sets
   `supportsForwardActionableRuleFallback = true`. Required for 2 and 3 to show any benefit at all.
5. **Done — Spring Data fragment relation modelled.** A constrained override lookup that finds
   nothing now retries once against the method's own declaring interface, when that interface is
   itself in the project. The re-keyed override cache was *not* reverted; the old behaviour was
   accidental and order-dependent. Recovers 2.
6. **Do not let an empty shallow result zero the scan** (`TaintAnalyzer.kt:143`) — fall back to an
   unrestricted full scan. Converts a silent total-recall loss into a bounded slowdown.
7. **Stop narrowing rule actions** (`SelectedTaintRulesProvider.kt:232`). Free recall, low risk.

Because 2 and 3 give back most of the shallow-scan speed the optimisations bought, on a project
already at the OOM watchdog, they must be benchmarked together with the memory work below.

Memory, in landing order:

4. **F5 — reassign instead of `clear()`** in `resetEdgeProcessingStorage`
   (`MethodAnalyzer.kt:1831-1836`), `TaintAnalysisUnitRunner.kt:99`,
   `SummaryEdgeSubscription.kt:861`; reset `methodEntryPointsCache` and
   `registeredResolvedCallees` in `resetApManager`, not only `cleanup()`. Mechanical,
   behaviour-identical.
5. **F6 — gate `MethodTaintMarkReachabilityIndex.addSummaryEdges` on `Phase.ShallowScan`**
   and clear `callers`/`callees` in `resetApManager`. Zero risk; the index is read only on
   the shallow fallback path.
6. **F3 — free the trace caches per vulnerability, not per phase**
   (`MethodAnalyzer.kt:228`, `JIRMethodAnalysisContext.kt:75`). Measured ~1.3 GB.
7. **F2 — cap the remaining per-analyzer BaseOnly memos.** The largest of them, the
   statement-collapse closure map, is gone with the optimisation; the rest are still uncapped.
   Cap, do not delete — removing them wholesale was measured at 124 s → 159 s.
8. **F1 — give the shallow scan a throttle that can fire**: a count-based criterion in
   `edgeExceedLimit`, or per-ap-mode depth semantics. This is the only change that *bounds*
   the phase. Without it the OOM recurs on any larger codebase.
9. **F7 — stop a preparatory phase's OOM from poisoning the exit code.** Land *after* F1,
   since alone it hides the recall risk rather than fixing it.

Trace quality:

10. In `MethodTraceSearch.kt:244`, track covered `(sink, source)` pairs separately from
    covered method nodes and accept a Pass-1 trace whenever its pair is uncovered, so every
    reachable source/sink pair gets a flow.
11. Penalise starts with `isStartOverApproximation = true`
    (`MethodTraceResolver.kt:778,830`) so a direct entry-point start outranks a
    boundary-hopped one.

## 10. Caveats on this data

- One run per side. This suite is known to be non-deterministic, and the trace representative
  is explicitly first-writer-wins under concurrency. Re-run before treating any single count
  as stable.
- The base results are dated 2026-08-13 and were reused from cache
  (`probe-thingsboard-base` shows `hit: true`); the new results ran fresh on 08-19.
  Finding-set comparisons hold; cross-day wall-clock comparisons are weak.
- When diffing SARIFs, match on `(ruleId, path, startLine, startColumn, endColumn)` and
  ignore the `codeFlows` count, or the report will overstate the damage as it did here.

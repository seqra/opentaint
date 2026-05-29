# Go FN-investigation pipeline Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the Go analyzer honor entry-point selection and fact-reachability export, add a benchmark batch driver, and produce a complete root-cause-clustered triage of all benchmark false negatives.

**Architecture:** The CLI flags already exist on `AbstractAnalyzerRunner` (`--debug-run-analysis-on-selected-entry-points`, `--debug-fact-reachability-sarif`) and `ProjectAnalyzerRunner` (`--rule-id`/`semgrepRuleId`), and all three already reach `GoProjectAnalysisOptions.common`. The work is making `GoProjectAnalyzer`/`GoTaintAnalyzer` *honor* them (the Go analyzer currently ignores `debugOptions`), then a `benchmarks/fn_investigate.py` driver, then the triage. We reuse the existing flags rather than adding `--entry-point` (the existing `--debug-run-analysis-on-selected-entry-points` IS the Java analog the spec referenced).

**Tech Stack:** Kotlin (analyzer), Python (batch script), the OpenTaint IFDS engine, SARIF.

---

## Preliminaries — environment

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
export PATH="/home/sobol/local/bin:$PATH"     # protoc 25.1
```
Test/build commands use `-x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks`. Source of truth: `docs/superpowers/specs/2026-05-28-go-fn-investigation-pipeline-design.md`.

Key facts confirmed by code inspection (do not re-derive):
- `GoProjectAnalysisOptions.common: CommonAnalysisOptions` already carries `debugOptions: DebugOptions?` and `semgrepRuleId`. `DebugOptions` has `factReachabilitySarif: Boolean` and `debugRunAnalysisOnSelectedEntryPoints: String?`.
- `--rule-id` already filters Go rules (`GoProjectAnalyzer.loadRules` → `options.common.loadSemgrepRules` → `parseSemgrepRules(…, semgrepRuleId, …)`). No work needed; the script just passes `--rule-id`.
- Java reference for entry-point filtering: `ProjectEntryPointsSelector.kt:21-37`. Java reference for fact-reachability: `ProjectAnalyzer.kt:146-149, 179-223` + `JIRTaintAnalyzer.statementsWithFacts()` (`JIRTaintAnalyzer.kt:262-276`) + `DebugFactReachabilitySarifGenerator.kt:16-74`.

---

## Task 1: Entry-point selection in GoProjectAnalyzer

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt` (`selectEntryPoints`)
- Test: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolverTest.kt` is the closest existing analyzer-level test; add a new focused test class instead — `core/src/test/kotlin/org/opentaint/go/sast/dataflow/EntryPointSelectionTest.kt`

The current `selectEntryPoints` (GoProjectAnalyzer.kt:91-95):
```kotlin
private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
    cp.packages.values
        .filter { it.isProject }
        .flatMap { it.functions }
        .filter { it.hasBody && !it.isSynthetic && it.parent == null }
```

- [ ] **Step 1: Write the failing test**

The test needs a built `GoIRProgram`. Reuse the `AnalysisTest` infrastructure pattern (it builds `cp` from the samples jar via `GoIRClient`). Because `selectEntryPoints` is `private`, test the behavior through a small `internal`-visible helper. Refactor the filter into an `internal` top-level function first (Step 3 makes it testable); the test calls that.

Create `EntryPointSelectionTest.kt`:
```kotlin
package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.go.sast.project.filterEntryPoints
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class EntryPointSelectionTest : AnalysisTest() {

    private fun allEntryPoints() =
        cp.packages.values.filter { it.isProject }
            .flatMap { it.functions }
            .filter { it.hasBody && !it.isSynthetic && it.parent == null }

    @Test fun nullSelectorReturnsAll() {
        val all = allEntryPoints()
        assertEquals(all.toSet(), filterEntryPoints(all, null).toSet())
    }

    @Test fun starSelectorReturnsAll() {
        val all = allEntryPoints()
        assertEquals(all.toSet(), filterEntryPoints(all, "*").toSet())
    }

    @Test fun fullNameSelectorReturnsExactlyOne() {
        val all = allEntryPoints()
        val target = all.first { it.fullName == "test.sample" }
        val filtered = filterEntryPoints(all, "test.sample")
        assertEquals(listOf(target), filtered)
    }

    @Test fun unknownNameSelectorReturnsEmpty() {
        val all = allEntryPoints()
        assertTrue(filterEntryPoints(all, "test.doesNotExist").isEmpty())
    }
}
```
(Confirm `test.sample` is a real entry-point fullName in the samples by dumping names once — `SampleTest` analyzes `test.sample`, so it is an entry point. If the exact fullName differs, adjust the literal after Step 2's dump.)

- [ ] **Step 2: Run test to verify it fails**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EntryPointSelectionTest' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -E 'PASSED|FAILED|error:|BUILD'
```
Expected: FAILS to compile — `filterEntryPoints` does not exist yet.

- [ ] **Step 3: Implement the filter**

In `GoProjectAnalyzer.kt`, add an `internal` top-level function and call it from `selectEntryPoints`:
```kotlin
internal fun filterEntryPoints(
    entryPoints: List<GoIRFunction>,
    selector: String?,
): List<GoIRFunction> {
    if (selector == null || selector == "*") return entryPoints
    return entryPoints.filter { it.fullName == selector }
}
```
Change `selectEntryPoints` to apply it and log zero-match:
```kotlin
private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> {
    val all = cp.packages.values
        .filter { it.isProject }
        .flatMap { it.functions }
        .filter { it.hasBody && !it.isSynthetic && it.parent == null }

    val selector = options.common.debugOptions?.debugRunAnalysisOnSelectedEntryPoints
    val filtered = filterEntryPoints(all, selector)
    if (selector != null && selector != "*" && filtered.isEmpty()) {
        logger.warn { "Entry-point selector matched no project function: '$selector'" }
    }
    return filtered
}
```
Confirm `options` is accessible in `selectEntryPoints` (it is a constructor property of `GoProjectAnalyzer`) and that `logger` is the companion `KLogging` logger already present in the file.

- [ ] **Step 4: Run test to verify it passes**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EntryPointSelectionTest' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -E 'PASSED|FAILED|BUILD'
```
Expected: all 4 PASS. If `fullNameSelectorReturnsExactlyOne` fails on the literal, dump the real fullName (add a `println(all.map { it.fullName })` temporarily, run, fix the literal, remove the println).

- [ ] **Step 5: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/EntryPointSelectionTest.kt
git commit -m "Go analyzer: honor --debug-run-analysis-on-selected-entry-points

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 2: Fact-reachability SARIF export in the Go analyzer

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt` (retain engine, become `AutoCloseable`, add `statementsWithFacts()`)
- Create: `core/src/main/kotlin/org/opentaint/go/sast/sarif/GoDebugFactReachabilitySarifGenerator.kt`
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt` (wire the flag)
- Test: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/FactReachabilityExportTest.kt`

**Reference:** `JIRTaintAnalyzer.statementsWithFacts()` (`JIRTaintAnalyzer.kt:262-276`), `DebugFactReachabilitySarifGenerator.kt:16-74`, and the test-side `AnalysisTest.printFactsAt` already in this repo (it does the exact `allUnits()`/`findUnitRunner`/`collectAllIntraProceduralFacts` walk).

- [ ] **Step 1: Write the failing test**

Create `FactReachabilityExportTest.kt`. It runs the analyzer on a known-tainted sample and asserts `statementsWithFacts()` is non-empty and contains a fact at the sink call. Mirror how `AnalysisTest.runAnalysisOnConfig` builds the engine, but go through `GoTaintAnalyzer`:
```kotlin
package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedAssignAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedCondition
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.configuration.go.serialized.GoSinkMetaData
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Result
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.ir.go.ext.findFunctionByFullName
import kotlin.test.Test
import kotlin.test.assertTrue

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class FactReachabilityExportTest : AnalysisTest() {

    @Test fun statementsWithFactsNonEmptyForTaintedSample() {
        val config = GoSerializedTaintConfig(
            source = listOf(GoSerializedRule.Source(
                function = GoNameMatcher.Simple("test/util.Source"),
                condition = null,
                taint = listOf(GoSerializedAssignAction("taint", PositionBaseWithModifiers.BaseOnly(Result))),
                info = null,
            )),
            sink = listOf(GoSerializedRule.Sink(
                function = GoNameMatcher.Simple("test/util.Sink"),
                condition = GoSerializedCondition.ContainsMark("taint", PositionBaseWithModifiers.BaseOnly(Argument(0))),
                trackFactsReachAnalysisEnd = emptyList(),
                id = "test-id",
                meta = GoSinkMetaData("Taint sink: test/util.Sink"),
                info = null,
            )),
        )
        val loaded = GoTaintConfiguration().apply { loadConfig(config) }
        val entry = cp.findFunctionByFullName("test.sample")!!
        GoTaintAnalyzer(cp, loaded, GoTestUnitResolver).use { analyzer ->
            analyzer.analyzeWithIfds(listOf(entry))
            val facts = analyzer.statementsWithFacts()
            assertTrue(facts.isNotEmpty(), "expected per-statement facts")
            assertTrue(facts.values.any { it.isNotEmpty() }, "expected at least one tainted statement")
        }
    }
}
```
NOTE: `AnalysisTest.TestUnitResolver` is `private`. Make it `internal` (or expose an `internal val goTestUnitResolver`) so this sibling test can construct `GoTaintAnalyzer` with the same resolver. Name the exposed resolver `GoTestUnitResolver`/`goTestUnitResolver` consistently.

- [ ] **Step 2: Run to verify it fails**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.FactReachabilityExportTest' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -E 'PASSED|FAILED|error:|BUILD'
```
Expected: FAILS to compile — `GoTaintAnalyzer` is not `AutoCloseable` and has no `statementsWithFacts()`.

- [ ] **Step 3: Refactor GoTaintAnalyzer to retain the engine + add statementsWithFacts()**

`analyzeWithIfds` currently builds the engine inside `engine.use { … }`, closing it on return. Refactor so the engine is created once, retained, and closed by `GoTaintAnalyzer.close()` (mirroring `JIRTaintAnalyzer` which is itself closeable and holds `ifdsEngine`):

```kotlin
class GoTaintAnalyzer(
    private val cp: GoIRProgram,
    private val taintConfig: GoTaintRulesProvider,
    private val unitResolver: UnitResolver<GoIRFunction>,
    private val externalMethodTracker: ExternalMethodTracker? = null,
    private val analysisTimeout: Duration = 1.minutes,
    private val cancellationTimeout: Duration = 10.seconds,
) : AutoCloseable {

    @Suppress("UNCHECKED_CAST")
    private val engine: TaintAnalysisUnitRunnerManager by lazy {
        val ifdsGraph = GoApplicationGraph(cp, unitResolver)
        TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(cp, taintConfig, externalMethodTracker = externalMethodTracker),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = unitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )
    }

    fun analyzeWithIfds(entryPoints: List<GoIRFunction>): List<VulnerabilityWithTrace> {
        val startMethods = entryPoints.map { MethodWithContext(it, EmptyMethodContext) }
        engine.runAnalysis(startMethods, timeout = analysisTimeout, cancellationTimeout = cancellationTimeout)
        val vulnerabilities = engine.getVulnerabilities()
        return engine.resolveVulnerabilityTraces(
            entryPoints.toSet(), vulnerabilities,
            resolverParams = TraceResolver.Params(),
            timeout = analysisTimeout, cancellationTimeout = cancellationTimeout,
        ).filter { it.trace != null }
    }

    fun statementsWithFacts(): Map<CommonInst, Set<FinalFactAp>> {
        val perEntry = hashMapOf<MethodEntryPoint, Map<CommonInst, Set<FinalFactAp>>>()
        engine.allUnits().forEach { unit ->
            val runner = engine.findUnitRunner(unit) ?: return@forEach
            runner.collectAllIntraProceduralFacts(perEntry)
        }
        val merged = hashMapOf<CommonInst, MutableSet<FinalFactAp>>()
        for ((_, stmtFacts) in perEntry) {
            for ((stmt, facts) in stmtFacts) merged.getOrPut(stmt) { hashSetOf() }.addAll(facts)
        }
        return merged
    }

    override fun close() {
        engine.close()
    }
}
```
Add imports: `org.opentaint.dataflow.ap.ifds.MethodEntryPoint`, `org.opentaint.dataflow.ap.ifds.access.FinalFactAp`. Confirm `TaintAnalysisUnitRunnerManager` is `AutoCloseable` (it is — it was used in `engine.use {}` before); if its close method has a different name, call that.

**Update the existing caller** `GoProjectAnalyzer.analyze` (it currently does `val traces = analyzer.analyzeWithIfds(entryPoints)` without `use`): wrap the analyzer in `.use { }` (Step 5).

- [ ] **Step 4: Create the SARIF generator**

Create `GoDebugFactReachabilitySarifGenerator.kt`, modelled on `DebugFactReachabilitySarifGenerator.kt:16-74` but using Go location resolution like the existing `GoSarifGenerator` (read `core/src/main/kotlin/org/opentaint/go/sast/sarif/GoSarifGenerator.kt` for how it maps a `GoIRInst`/`GoInstLocation` to a SARIF physical location + URI relative to `project.projectDir`). Signature:
```kotlin
class GoDebugFactReachabilitySarifGenerator(
    private val sarifOptions: SarifGenerationOptions,
    private val projectDir: Path,
) {
    fun generateSarif(output: OutputStream, facts: Map<CommonInst, Set<FinalFactAp>>) { … }
}
```
Emit one SARIF `result` per `(statement, fact)` pair: ruleId `s_<index>`, message = `fact.toString()`, location from `(stmt.location as GoInstLocation).position` (file + line). Reuse whatever SARIF data classes `GoSarifGenerator` already uses (don't introduce a second SARIF model). Skip statements with empty fact sets.

- [ ] **Step 5: Wire the flag in GoProjectAnalyzer.analyze**

Read the current `analyze()` body. Replace the bare `GoTaintAnalyzer(...)` + `analyzer.analyzeWithIfds(...)` with a `use` block, and after producing traces, when the flag is set, write the report:
```kotlin
GoTaintAnalyzer(
    cp = cp,
    taintConfig = rulesProvider,
    unitResolver = GoUnitResolver(),
    externalMethodTracker = tracker,
    analysisTimeout = options.common.ifdsAnalysisTimeout,
).use { analyzer ->
    val entryPoints = selectEntryPoints(cp)
    logger.info { "Selected ${entryPoints.size} Go entry points" }
    val traces = analyzer.analyzeWithIfds(entryPoints)
    logger.info { "Go analysis produced ${traces.size} traces" }
    writeReport(traces)
    if (options.common.debugOptions?.factReachabilitySarif == true) {
        val facts = analyzer.statementsWithFacts()
        (resultDir / "debug-ifds-fact-reachability.sarif").outputStream().use { out ->
            GoDebugFactReachabilitySarifGenerator(options.common.sarifGenerationOptions, project.projectDir)
                .generateSarif(out, facts)
        }
        logger.info { "Wrote Go fact-reachability SARIF (${facts.size} statements)" }
    }
    tracker?.let { writeExternalMethodsYaml(it.getExternalMethods()) }
}
```
Keep the existing `ProjectAnalysisStatus.OK`/exception handling around it.

- [ ] **Step 6: Run the test to verify green**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.FactReachabilityExportTest' --tests 'org.opentaint.go.sast.dataflow.SampleTest' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | grep -E 'PASSED|FAILED|BUILD'
```
Expected: `FactReachabilityExportTest` PASSES and `SampleTest` (existing) still PASSES (the GoTaintAnalyzer refactor didn't break normal analysis).

- [ ] **Step 7: Full Go dataflow regression**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.*' -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | tail -6
```
Expected: BUILD SUCCESSFUL, no new failures (the AutoCloseable refactor preserves analysis behavior).

- [ ] **Step 8: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt \
  core/src/main/kotlin/org/opentaint/go/sast/sarif/GoDebugFactReachabilitySarifGenerator.kt \
  core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/FactReachabilityExportTest.kt \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/AnalysisTest.kt
git commit -m "Go analyzer: port --debug-fact-reachability-sarif

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 3: Benchmark FN-investigation batch script

**Files:**
- Create: `benchmarks/fn_investigate.py`
- Reference: `benchmarks/scan.sh` (jar paths, GOIR_SERVER_BINARY, flags), `benchmarks/compare.py` (FN extraction logic + `cwe_of`).

The script must rebuild nothing — it consumes the already-built jars and project models. It runs the analyzer once per FN, scoped to one entry point + one rule + fact-reachability.

- [ ] **Step 1: Build the jars + server (prerequisite, not part of the script)**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core && export PATH="/home/sobol/local/bin:$PATH"
./gradlew :projectAnalyzerJar :opentaint-jvm-autobuilder:projectAutoBuilderJar :opentaint-ir:go:buildGoServer -x ':opentaint-ir:python:createPirServerVenv' 2>&1 | grep -E 'BUILD'
```

- [ ] **Step 2: Dump entry-point full names to lock the format**

Run the analyzer once on a benchmark with a deliberately-unmatched selector and read the warn log, OR add a one-off: run a normal scan and grep the analyzer log for "Selected N Go entry points", then temporarily run with `--debug-run-analysis-on-selected-entry-points '*'` and inspect. Simplest: write a 5-line throwaway that lists `cp.packages...functions...fullName` is overkill — instead, run one FN through the analyzer with a guessed name; if it warns "matched no project function", read the controller's package + type from the `.go` and the go.mod module path to construct the exact `(*<module>/controllers.BenchmarkTestNNNN).ServeHTTP` form. Record the confirmed format in a comment at the top of `fn_investigate.py`.

- [ ] **Step 3: Write the script**

`benchmarks/fn_investigate.py` — structure (complete, no placeholders):
```python
#!/usr/bin/env python3
"""Per-FN fact-reachability investigation driver.

For each false negative on a benchmark, run the analyzer scoped to that
FN's single entry point and single CWE rule with --debug-fact-reachability-sarif,
then extract the mechanical FN signal into fn-triage.jsonl.

Entry-point full-name format (confirmed on the benchmarks):
  method handler:  (*<module>/controllers.<Type>).ServeHTTP   (owasp)
  top-level func:  <module>/controllers.<Func>                 (owasp doGet-style)
  beego method:    (*<module>/controllers.<Type>).Get|Post     (sec-code)
"""
import json, re, subprocess, sys, pathlib
from collections import defaultdict

REPO = pathlib.Path("/drive-testcomp/opentaint-go-rules/opentaint")
BENCH = pathlib.Path("/drive-testcomp/opentaint-go-rules/benchmarks")
ANALYZER_JAR = REPO / "core/build/libs/opentaint-project-analyzer.jar"
AUTOBUILDER_JAR = REPO / "core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder.jar"
SERVER = REPO / "core/opentaint-ir/go/go-ssa-server/go-ssa-server"
RULES = BENCH / "rules"

CWE_RULE = {
    "CWE-22": "go.security.go-path-traversal",
    "CWE-78": "go.security.go-command-injection",
    "CWE-79": "go.security.go-reflected-xss",
    "CWE-89": "go.security.go-sql-injection",
}

# (script body: see steps below for each function)
```

Implement these functions:
- `cwe_of(rule_id)` — copy from `compare.py`.
- `fn_files(bench_dir)` — run `compare.py` logic inline (import or re-implement) to return `{cwe: [uri,...]}` of truth-fail URIs NOT in the report (the FNs). Reuse `compare.py`'s SARIF loading; simplest is `from compare import` if importable, else inline the ~20 lines.
- `module_path(bench_dir)` — read `go.mod` first line `module <path>`.
- `entry_point_names(go_file, module_path)` — regex the `.go` source:
  - `func \(\w+ \*?(\w+)\) ServeHTTP\(` → `(*<module>/controllers.<Type>).ServeHTTP` (and the value-receiver form without `*` if no `*`).
  - `^func (BenchmarkTest\w+)\(w http\.ResponseWriter` → `<module>/controllers.<Func>`.
  - beego: `func \(\w+ \*?(\w+)\) (Get|Post)\(\)` → `(*<module>/controllers.<Type>).<Method>`.
  Return the list of candidate full names (usually one). The `controllers` package segment comes from the file's `package` clause + its directory relative to module root; for these benchmarks it is `controllers`.
- `run_one(bench_dir, go_file, cwe, ep_name)` — invoke:
  ```python
  out_dir = bench_dir / ".opentaint/fn-runs" / pathlib.Path(go_file).stem
  out_dir.mkdir(parents=True, exist_ok=True)
  env = {**os.environ, "GOIR_SERVER_BINARY": str(SERVER)}
  cmd = ["opentaint", "--experimental", "scan",
         "--project-model", str(bench_dir/".opentaint/project"),
         "--analyzer-jar", str(ANALYZER_JAR),
         "--autobuilder-jar", str(AUTOBUILDER_JAR),
         "--ruleset", str(RULES),
         "--rule-id", CWE_RULE[cwe],
         "--debug-run-analysis-on-selected-entry-points", ep_name,
         "--debug-fact-reachability-sarif",
         "--track-external-methods",
         "-o", str(out_dir/"report.sarif")]
  r = subprocess.run(cmd, env=env, capture_output=True, text=True, timeout=300)
  return out_dir, r.returncode
  ```
- `extract_signal(out_dir, go_file)` — read `out_dir/debug-ifds-fact-reachability.sarif` (per-statement facts) + `out_dir/external-methods-without-rules.yaml`. Compute:
  - `source_matched`: any fact result located in `go_file`.
  - `finding`: `out_dir/report.sarif` has ≥1 result.
  - `death_instr` / `last_tainted_instr`: walk the fact results in `go_file` ordered by line; `last_tainted` = highest-line statement with a fact, `death_instr` = the next statement after it in source with no fact (best-effort; record the SARIF message text of both).
  - `externals_on_path`: method names in `external-methods-without-rules.yaml`.
  Return a dict.
- `main(bench_name)` — loop FNs, for each: derive names, pick first that the analyzer matches (non-empty fact SARIF), run, extract, append a row to `fn-triage.jsonl`. Rows for unmatched/unparsed/errored FNs carry a `status` of `skip:no-entrypoint` / `skip:entrypoint-unmatched` / `error:analyzer` per the spec. Print a running count.

Add `import os`. Make the script accept the benchmark name as `argv[1]` (default both).

- [ ] **Step 4: Smoke-test on 3 FNs**

Temporarily cap the loop to the first 3 owasp FNs (or add a `--limit N` arg). Run:
```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks && python3 fn_investigate.py go-owasp-converted-mutated --limit 3
head fn-triage.jsonl
```
Expected: 3 JSONL rows, each with a non-empty `entryPoint`, a `source_matched` boolean, and either a `death_instr` or a `status`. Confirm at least one row shows `source_matched: true` (proves entry-point selection + fact SARIF work end-to-end through the CLI).

- [ ] **Step 5: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add benchmarks/fn_investigate.py
git commit -m "benchmarks: add per-FN fact-reachability investigation driver

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Task 4: Run the investigation and produce the triage

**Files:**
- Create: `benchmarks/fn-triage.jsonl` (generated, committed for the record)
- Create: `docs/superpowers/specs/2026-05-28-go-fn-triage.md` (the clustered report)

- [ ] **Step 1: Run the full batch on both benchmarks**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
python3 fn_investigate.py go-owasp-converted-mutated
python3 fn_investigate.py go-sec-code-mutated
wc -l fn-triage.jsonl
```
Expected: one row per FN (~112 owasp + 3 sec), minus any `skip:no-entrypoint`. This is long-running (one analyzer JVM per FN); run in the background and checkpoint.

- [ ] **Step 2: Classify each FN**

From `fn-triage.jsonl`, assign each FN the primary category per the spec taxonomy (`missing-source` / `missing-sink` / `missing-propagator` / `engine-fn` / `unsupported-construct` / `not-reachable`) using the mechanical signal + inspection of the death instruction for the ambiguous ones. Sub-group `engine-fn` by death-instruction IR kind.

- [ ] **Step 3: Write the triage report**

`docs/superpowers/specs/2026-05-28-go-fn-triage.md`:
- Per-sample table: file · cwe · entryPoint · category · death point.
- Clustered summary: category → count; per cluster one representative sample with its trace excerpt.
- Residual sets: `skip:*` and `error:*` FNs listed for manual follow-up.
- A short "next-round candidates" section naming the largest actionable clusters (handed to a follow-up brainstorm — no fixes here).

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add benchmarks/fn-triage.jsonl docs/superpowers/specs/2026-05-28-go-fn-triage.md
git commit -m "Add complete benchmark FN root-cause triage

Co-Authored-By: Claude Opus 4.8 (1M context) <noreply@anthropic.com>"
```

---

## Final review

After all tasks, dispatch a code review over `git diff abf3b5ed..HEAD` focused on: the GoTaintAnalyzer AutoCloseable refactor doesn't leak the engine or change analysis results (full Go suite still green); the entry-point filter logs zero-matches; the script's entry-point-name derivation matches the analyzer's `fullName` format; the triage taxonomy is applied consistently. Then use superpowers:finishing-a-development-branch.

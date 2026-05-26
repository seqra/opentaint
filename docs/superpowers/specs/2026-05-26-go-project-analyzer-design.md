# Go Project Analyzer — Design

## Goal

Wire the Go SAST pipeline end-to-end behind the same CLI surface (`ProjectAnalyzerRunner`,
`ProjectAutoBuilder`) used today for Java/JVM, so a single `opentaint` invocation can:

1. Auto-detect Go modules in an arbitrary directory tree.
2. Build a `GoProject` (via `GoIRClient`).
3. Run Semgrep-derived Go taint rules + bundled passThrough config + user-supplied
   approximations.
4. Emit a SARIF report and (optionally) external-methods YAML lists.
5. Be validated to >70% TP on the `go-owasp-converted-mutated` and `go-sec-code-mutated`
   benchmarks.

## Non-goals

- Symbolic execution (JVM-only feature).
- Java code-based approximations on Go (Go has no equivalent yet).
- Spring/JIR-specific options (`projectKind`, `experimentalAAInterProcCallDepth`, SE).

## Architecture

### Shared options (composition)

Today `ProjectAnalysisOptions` mixes language-neutral knobs (semgrep rules,
ifds timeout, sarif options, debug, external-method tracking, approximation
YAMLs) with JVM-specific ones (SE, JIR approximation classpath, project kind).

We extract the neutral subset into a new **data class** and reference it from
both option types — interfaces would force us to re-declare every field on every
implementation, which defeats the goal.

```kotlin
data class CommonAnalysisOptions(
    val customApproximationConfig: List<Path> = emptyList(),
    val semgrepRuleSet: List<Path> = emptyList(),
    val semgrepRuleLoadTrace: Path? = null,
    val semgrepSeverity: List<Severity> = emptyList(),
    val semgrepRuleId: List<String> = emptyList(),
    val trackExternalMethods: Boolean = false,
    val ifdsAnalysisTimeout: Duration = Duration.ZERO,
    val ifdsApMode: ApMode = ApMode.Tree,
    val debugOptions: DebugOptions? = null,
    val sarifGenerationOptions: SarifGenerationOptions = SarifGenerationOptions(),
)
```

- `ProjectAnalysisOptions` (JVM) holds `val common: CommonAnalysisOptions` plus
  the JVM-only knobs (`cwe`, SE, `experimentalAAInterProcCallDepth`,
  `projectKind`, `storeSummaries`, `approximationOptions`). All existing call
  sites that read shared fields are rewritten to go through `.common`.
- New `GoProjectAnalysisOptions` (Go) holds `val common: CommonAnalysisOptions`
  and nothing else for v1.
- Shared loaders such as `loadSemgrepRules()` become extensions on
  `CommonAnalysisOptions`, parameterised by the language strategy.

### `GoTaintRulesProvider` becomes an interface

To support rule combination on Go (analogous to Java's `JIRCombinedTaintRulesProvider`),
we promote the current concrete `GoTaintRulesProvider` class to an interface.

```kotlin
interface GoTaintRulesProvider {
    fun sourceRulesForGlobal(globalName: String): List<TaintRule.GlobalReadSource>
    fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Source>
    fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRule.Sink>
    fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRule.PassThrough>
    fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Cleaner>
}
```

`GoTaintConfiguration` (the rule store) implements `GoTaintRulesProvider` directly
by delegating to its existing `*Function`/`*Global` lookups (rename of internal
methods if needed, no behaviour change).

New `GoCombinedTaintRulesProvider(base, combined, options)` mirrors the JVM
`JIRCombinedTaintRulesProvider`:

- Default modes: `passThrough = EXTEND`, `source/sink/cleaner = OVERRIDE`,
  matching the JVM defaults.
- Used by `GoProjectAnalyzer` only when the user supplied custom
  approximation YAMLs; otherwise the provider returned is the plain
  `GoTaintConfiguration`.

### Rule loading on Go

Mirrors the JVM `preloadRules` → `loadTaintConfig` chain:

1. `SemgrepRuleLoader(listOf(GoLanguageStrategy()))` walks `semgrepRuleSet`,
   producing `TaintRuleFromSemgrep<GoSerializedItem>` entries.
2. Each rule is converted into `GoSerializedTaintConfig` via a new top-level
   extension `TaintRuleFromSemgrep<GoSerializedItem>.toGoSerializedTaintConfig()`
   in `opentaint-go-querylang/src/main/.../conversion/GoTaintRuleEmit.kt`
   (replaces the test-only `GoTaintRuleEmitter` class).
3. All converted configs are loaded into a single `GoTaintConfiguration` (call
   it `userConfig`).
4. The bundled `GoConfigLoader.getConfig()` passThrough rules are loaded into
   `userConfig` first so user rules can extend them.
5. User-supplied `customApproximationConfig` YAMLs are parsed via a new public
   `loadGoSerializedTaintConfig(InputStream): GoSerializedTaintConfig` helper
   (extracted from the private parser inside `GoConfigLoader`). Approximation
   YAMLs only carry `passThrough` entries by definition (see
   `create-yaml-config` skill); no other rule kinds need to deserialize, so the
   `GoSerializedTaintConfig.@Serializable` gap is irrelevant here.
6. If approximation YAMLs are present, they are loaded into a separate
   `GoTaintConfiguration` (call it `approxConfig`) and exposed through
   `GoCombinedTaintRulesProvider(userConfig, approxConfig, defaultOptions)`.
   Otherwise the analyzer receives `userConfig` directly.

### Analyzer wiring

`GoProjectAnalyzer.analyze()`:

```
GoIRClient().use { client ->
    val cp = client.buildFromDir(project.projectDir, "./...")
    val provider = loadRules(...)
    val tracker = if (options.common.trackExternalMethods) ExternalMethodTracker() else null
    val analyzer = GoTaintAnalyzer(
        cp = cp,
        taintConfig = provider,
        unitResolver = GoUnitResolver(cp.packages.keys.toSet()),
        externalMethodTracker = tracker,
        analysisTimeout = options.common.ifdsAnalysisTimeout,
    )
    val traces = analyzer.analyzeWithIfds(entryPoints)
    writeSarif(traces)
    if (tracker != null) writeExternalMethodsYaml(tracker.getExternalMethods())
}
```

- `GoTaintAnalyzer` gets a new optional `externalMethodTracker` constructor
  parameter that it forwards to `GoAnalysisManager`.
- External-methods YAML format and filenames mirror the JVM analyzer
  (`external-methods-without-rules.yaml`, `external-methods-with-rules.yaml`)
  so the existing `analyze-findings` skill applies unchanged.

### Runner dispatch

`AbstractAnalyzerRunner`:

- New abstract `analyzeGoProject(project: GoProject, outputDir: Path, debugOptions: DebugOptions): ProjectAnalysisStatus`.
- Existing fold over `goProjects` swaps the warn-only stub for
  `runGoProjectAnalysisRecursively(gp)` (symmetric to the Java helper).

`ProjectAnalyzerRunner.analyzeGoProject`:

- Builds a `GoProjectAnalysisOptions` whose `common` field comes from the same
  CLI flags as the JVM run (approximations, semgrep ruleset/severity/id/trace,
  track-external, IFDS timeout/AP mode, debug, SARIF options). JVM-only flags
  (`cwe`, `useSymbolicExecution`, `dataflowApproximations`,
  `experimentalAAInterProcCallDepth`, `projectKind`) are ignored.

### Autobuilder Go support

`ProjectAutoBuilder.main()` already runs `ProjectResolver.resolveProject` for Java.
We add a parallel scan for Go:

```kotlin
private fun findGoProjects(root: Path): List<GoProject> {
    val out = mutableListOf<GoProject>()
    root.visitFileTree {
        onPreVisitDirectory { dir, _ ->
            when {
                dir.isHiddenSubDirOf(root) -> SKIP_SUBTREE
                (dir / "go.mod").exists() -> {
                    out += GoProject(projectDir = dir)
                    SKIP_SUBTREE     // do not descend into Go sub-modules from this one
                }
                else -> CONTINUE
            }
        }
    }
    return out
}
```

Resulting `Project` carries both `javaProjects` and `goProjects`; the same root
directory may hold both kinds without conflict (Java resolution operates on
build-tool roots; Go resolution operates on `go.mod` roots — they don't fight).

### Module dependency changes

`core/build.gradle.kts` currently has `:opentaint-go-querylang` as a
`testImplementation`. To use `GoLanguageStrategy` and the new top-level emitter
from production code, this must become an `implementation`. We also add
`org.opentaint.config:go-config` so the bundled passThrough config loads from
production code (`GoConfigLoader.getConfig()` lives in that module).

No other modules need new dependencies: the new emitter file lives in
`opentaint-go-querylang/src/main/`, which already depends on
configuration-rules-go and opentaint-go-dataflow.

## Wiring the modified jars into `opentaint`

`opentaint compile` and `opentaint scan` download pinned production jars by
default. To exercise our refactor end-to-end on the benchmarks, both commands
must be pointed at the locally built jars via the experimental dev overrides:

```bash
./gradlew :core:projectAnalyzerJar :core:opentaint-jvm-autobuilder:autobuilderJar
ANALYZER_JAR=$(pwd)/core/build/libs/opentaint-project-analyzer-all.jar
AUTOBUILDER_JAR=$(pwd)/core/opentaint-jvm-autobuilder/build/libs/opentaint-jvm-autobuilder-all.jar

opentaint --experimental compile <bench> \
  --analyzer-jar "$ANALYZER_JAR" \
  --autobuilder-jar "$AUTOBUILDER_JAR" \
  -o .opentaint/project

opentaint --experimental scan --project-model .opentaint/project \
  --analyzer-jar "$ANALYZER_JAR" \
  --autobuilder-jar "$AUTOBUILDER_JAR" \
  -o .opentaint/results/report.sarif \
  --ruleset builtin --ruleset .opentaint/rules \
  --track-external-methods
```

Until both jars are explicitly forwarded, `opentaint` falls back to the bundled
artifacts and our Go pipeline is invisible.

## Benchmark verification phase

For each of `go-owasp-converted-mutated` and `go-sec-code-mutated`:

1. Clone fresh into `/drive-testcomp/opentaint-go-rules/benchmarks/<name>`.
2. `opentaint --experimental compile … --analyzer-jar … --autobuilder-jar …`
   → `.opentaint/project` for the benchmark.
3. Initial scan with built-in rules only (locally built jars) → baseline SARIF
   + external-methods YAMLs.
4. Compare baseline SARIF to `truth.sarif` (in benchmark root; `kind=pass`
   means FP, `kind=fail` means TP). A small script reports per-rule and per-CWE
   TP/FP counts.

This first phase only validates that the end-to-end Go pipeline is wired
correctly — we expect ~0 findings because **no Go rules ship in the
production rule set today**. Rule authoring is the next phase.

## Second brainstorming round before rule development

Once the analyzer runs cleanly on both benchmarks and produces SARIF (even an
empty one), the remaining work — designing Go-side detection rules and
approximations — is creative enough to merit its own brainstorming pass before
implementation. We **must** invoke the `superpowers:brainstorming` skill again
at that boundary to:

- Inventory the benchmark vulnerability classes (CWEs, languages used to
  exploit them, what idioms appear repeatedly).
- Decide the rule taxonomy (one rule per CWE? per source/sink pair? library
  split?) and the directory layout under `.opentaint/rules/go/`.
- Pick the order in which classes are tackled and define exit criteria per
  class beyond the global >70% TP target.

Do not skip this round even if the production code is fully wired — the rule
language is sufficiently expressive that ad-hoc authoring drifts without a
deliberate taxonomy.

## Iteration plan (rule development phase, post-second-brainstorm)

Following the `analyze-findings` skill, in priority order:

1. Author new rules under `.opentaint/rules/go/...` following the
   `samples-go-massive/<class>` patterns (one source, one sink, optional cleaner).
2. Add passThrough YAMLs for generic propagators in
   `external-methods-without-rules.yaml` (collections, builders, fmt helpers).
3. Re-scan; loop until TP fraction >70%.
4. Commit each rule/approximation batch separately to preserve attribution.

## Testing strategy

- `GoMassiveSampleTest` currently has 27 failing tests on `main`; this refactor
  is not expected to change that count. We only need to ensure no *new*
  regressions in that suite after the rule-store refactor (provider interface
  + emitter relocation).
- Add a tiny unit test for `findGoProjects` covering: single root, nested
  modules, hidden dirs, mixed Java+Go.
- E2E: run the analyzer on one of `samples-go-massive/*` as a smoke test
  before attacking the real benchmarks.

## Risks / open questions

- **External method tracking parity**: `GoAnalysisManager` already accepts an
  `ExternalMethodTracker`, but no production code threads one in. Surface-area
  change: one optional constructor parameter on `GoTaintAnalyzer`.
- **Module promotion**: making `:opentaint-go-querylang` an `implementation`
  dependency of `core` increases the production classpath; the antlr runtime,
  grammar code, and conversion utilities ship in the final fat jar. Acceptable
  given the new analyzer entry point already needs them at runtime.

## File-level change list

Touch only the following files.

- new: `core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/GoTaintRuleEmit.kt`
- delete: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/GoTaintRuleEmitter.kt`
- update: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/{GoMassiveSampleTest,GoSampleBasedTest}.kt`
- update: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/pattern/{GoRuleEmitTest,conversion/go/GoTaintRuleEmitterTest}.kt`
- update: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoSemgrepReachabilityTest.kt`
- update: `core/opentaint-config/go-config/.../GoConfigLoader.kt` (expose `loadGoSerializedTaintConfig`)
- new: `core/opentaint-dataflow-core/opentaint-go-dataflow/.../GoCombinedTaintRulesProvider.kt`
- update: `core/opentaint-dataflow-core/opentaint-go-dataflow/.../GoTaintRulesProvider.kt` (class → interface)
- update: `core/opentaint-dataflow-core/opentaint-go-dataflow/.../GoTaintConfiguration.kt` (implements provider)
- new: `core/src/main/kotlin/org/opentaint/jvm/sast/project/CommonAnalysisOptions.kt`
- new: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalysisOptions.kt`
- update: `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisOptions.kt`
- update: `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/LoadSemgrepRules.kt`
- update: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt`
- update: `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt`
- update: `core/src/main/kotlin/org/opentaint/jvm/sast/runner/AbstractAnalyzerRunner.kt`
- update: `core/src/main/kotlin/org/opentaint/jvm/sast/runner/ProjectAnalyzerRunner.kt`
- update: `core/opentaint-jvm-autobuilder/src/main/kotlin/org/opentaint/project/ProjectAutoBuilder.kt`
- update: `core/build.gradle.kts` (dependency scope)

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

### Shared options

Today `ProjectAnalysisOptions` mixes language-neutral knobs (semgrep rules,
ifds timeout, sarif options, debug, external-method tracking, approximation
YAMLs) with JVM-specific ones (SE, JIR approximation classpath, project kind).

We extract the neutral subset into a new interface `CommonAnalysisOptions`:

```kotlin
interface CommonAnalysisOptions {
    val customApproximationConfig: List<Path>
    val semgrepRuleSet: List<Path>
    val semgrepRuleLoadTrace: Path?
    val semgrepSeverity: List<Severity>
    val semgrepRuleId: List<String>
    val trackExternalMethods: Boolean
    val ifdsAnalysisTimeout: Duration
    val ifdsApMode: ApMode
    val debugOptions: DebugOptions?
    val sarifGenerationOptions: SarifGenerationOptions
}
```

- `ProjectAnalysisOptions` (existing, JVM) implements it without losing any field.
- New `GoProjectAnalysisOptions` (Go) implements it; no extra fields for v1.
- `loadSemgrepRules()` becomes an extension on `CommonAnalysisOptions` parameterised
  by the language strategy, removing the only duplicated bit of Java-only logic.

### Rule loading on Go

Mirrors the JVM `preloadRules` → `loadTaintConfig` chain:

1. `SemgrepRuleLoader(listOf(GoLanguageStrategy()))` walks `semgrepRuleSet`,
   producing `TaintRuleFromSemgrep<GoSerializedItem>` entries.
2. Each rule is converted into `GoSerializedTaintConfig` via a new top-level
   extension `TaintRuleFromSemgrep<GoSerializedItem>.toGoSerializedTaintConfig()`
   (replaces the test-only `GoTaintRuleEmitter` class).
3. All converted configs are loaded into a single `GoTaintConfiguration`.
4. The bundled `GoConfigLoader.getConfig()` passThrough rules are loaded on top.
5. User-supplied `customApproximationConfig` YAMLs are parsed via a new public
   `loadGoSerializedTaintConfig(InputStream): GoSerializedTaintConfig` helper
   (extracted from the private parser inside `GoConfigLoader`) and loaded last.
   `GoTaintConfiguration.loadConfig` is additive — for v1, custom passThrough
   rules stack on top of the bundled ones rather than overriding them. JVM-style
   `CombinationMode.OVERRIDE` parity is out of scope; a follow-up can add it
   once a concrete override case appears.
6. The resulting `GoTaintRulesProvider` is handed to `GoTaintAnalyzer`.

### Analyzer wiring

`GoProjectAnalyzer.analyze()`:

```
GoIRClient().use { client ->
    val cp = client.buildFromDir(project.projectDir, "./...")
    val provider = loadRules(...)
    val tracker = if (options.trackExternalMethods) ExternalMethodTracker() else null
    val analyzer = GoTaintAnalyzer(
        cp = cp,
        taintConfig = provider,
        unitResolver = GoUnitResolver(cp.packages.keys.toSet()),
        externalMethodTracker = tracker,                    // new param, threaded into GoAnalysisManager
        analysisTimeout = options.ifdsAnalysisTimeout,
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

- Builds a `GoProjectAnalysisOptions` from the same CLI flags as the JVM run
  (approximations, semgrep ruleset/severity/id/trace, track-external, IFDS timeout/AP mode,
  debug, SARIF options). JVM-only flags (`cwe`, `useSymbolicExecution`, `dataflowApproximations`,
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

## Rule iteration plan (benchmarks)

For each of `go-owasp-converted-mutated` and `go-sec-code-mutated`:

1. Clone fresh into `/drive-testcomp/opentaint-go-rules/benchmarks/<name>`.
2. `opentaint compile` → `.opentaint/project` for the benchmark.
3. Initial scan with built-in rules only → baseline SARIF + external-methods YAMLs.
4. Compare baseline SARIF to `truth.sarif` (pass=FP, fail=TP) via a small script
   that reports per-rule and per-CWE TP/FP counts.
5. Iterate, in the order recommended by the `analyze-findings` skill:
   - Author new rules under `.opentaint/rules/go/...` following the
     `samples-go-massive/<class>` patterns (one source, one sink, optional cleaner).
   - Add passThrough YAMLs for generic propagators in
     `external-methods-without-rules.yaml` (collections, builders, fmt helpers).
   - Re-scan; loop until TP fraction >70%.
6. Commit each rule/approximation batch separately to preserve attribution.

## Testing strategy

- Reuse `GoMassiveSampleTest` to ensure the refactored emitter still passes.
- Add a tiny unit test for `findGoProjects` covering: single root, nested modules,
  hidden dirs, mixed Java+Go.
- E2E: run the analyzer on one of `samples-go-massive/*` as a smoke test before
  attacking the real benchmarks.

## Risks / open questions

- **Custom approximation YAML format**: `GoSerializedTaintConfig` is not
  `@Serializable`. The new helper will parse only the `passThrough` section
  (matching today's `GoConfigLoader` behaviour); source/sink/cleaner custom
  YAMLs are out of scope until the serialized types become `@Serializable`.
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

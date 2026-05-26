# Go Project Analyzer Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Wire the existing Go SAST pipeline behind `ProjectAnalyzerRunner` / `ProjectAutoBuilder`, share analyzer options with the JVM path via composition, and produce a SARIF on two real benchmarks as a smoke test.

**Architecture:** A reusable `CommonAnalysisOptions` data class is held by composition inside both `ProjectAnalysisOptions` (JVM) and a new `GoProjectAnalysisOptions`. `GoTaintRulesProvider` becomes an interface; the existing `GoTaintConfiguration` implements it directly, and a new `GoCombinedTaintRulesProvider` mirrors the JVM combiner for user approximations. Semgrep loading and external-methods YAML output become language-agnostic helpers. The autobuilder gains a `go.mod` scanner; the runner dispatches both Java and Go.

**Tech Stack:** Kotlin (JVM 11), Gradle (`core/gradlew`), kaml, clikt, kotlinx-serialization, sarif4k, antlr.

Working directory for every step: `/drive-testcomp/opentaint-go-rules/opentaint`. All `./gradlew` invocations run from `/drive-testcomp/opentaint-go-rules/opentaint/core` (that's where the Gradle wrapper lives). Use absolute paths when in doubt.

---

## File Structure

Code changes by file (matches the spec's "File-level change list"):

| File | Responsibility |
|------|---------------|
| `core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/GoTaintRuleEmit.kt` (new) | Top-level extensions converting `TaintRuleFromSemgrep<GoSerializedItem>` → `GoSerializedTaintConfig` / `GoTaintConfiguration`. |
| `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/GoTaintRuleEmitter.kt` (delete) | Test-only class — replaced by the new top-level extension. |
| `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/{GoMassiveSampleTest, GoSampleBasedTest}.kt`, `…/semgrep/pattern/{GoRuleEmitTest, conversion/go/GoTaintRuleEmitterTest}.kt`, `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoSemgrepReachabilityTest.kt` (update) | Switch from `GoTaintRuleEmitter().emit(rule)` → `rule.toGoTaintConfiguration()`. |
| `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoTaintRulesProvider.kt` (update) | Class → interface. |
| `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoTaintConfiguration.kt` (update) | Add `: GoTaintRulesProvider` and provider-facing methods that delegate to existing internal lookups. |
| `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoCombinedTaintRulesProvider.kt` (new) | EXTEND/OVERRIDE/IGNORE combiner of two `GoTaintRulesProvider`s. |
| `core/opentaint-config/go-config/src/main/kotlin/org/opentaint/go/config/GoConfigLoader.kt` (update) | Extract a public `loadGoSerializedTaintConfig(InputStream)` from the existing private passThrough parser. |
| `core/src/main/kotlin/org/opentaint/jvm/sast/project/CommonAnalysisOptions.kt` (new) | Language-neutral options data class. |
| `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalysisOptions.kt` (new) | Holds `common: CommonAnalysisOptions`. |
| `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisOptions.kt` (update) | Holds `common: CommonAnalysisOptions`; JVM-only fields remain at top level. |
| `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/LoadSemgrepRules.kt` (update) | `loadSemgrepRules(strategy)` extension on `CommonAnalysisOptions`. |
| `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt` (update) | Accept optional `externalMethodTracker` and forward into `GoAnalysisManager`. |
| `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt` (update) | Full implementation: rule loading, external-methods YAML, SARIF. |
| `core/src/main/kotlin/org/opentaint/jvm/sast/runner/AbstractAnalyzerRunner.kt` (update) | Add abstract `analyzeGoProject`; dispatch Go projects. |
| `core/src/main/kotlin/org/opentaint/jvm/sast/runner/ProjectAnalyzerRunner.kt` (update) | Implement `analyzeGoProject` from existing CLI flags. |
| `core/opentaint-jvm-autobuilder/src/main/kotlin/org/opentaint/project/ProjectAutoBuilder.kt` (update) | Walk for `go.mod` and emit `goProjects`. |
| `core/build.gradle.kts` (update) | Promote `:opentaint-go-querylang` to `implementation` and add `org.opentaint.config:go-config`. |

Tests added under existing source trees alongside the code they exercise.

---

## Phase 1 — Refactor Go rule infrastructure (no behaviour change)

### Task 1: Move `GoTaintRuleEmitter` to main as top-level extensions

**Files:**
- Create: `core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/GoTaintRuleEmit.kt`
- Delete: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/GoTaintRuleEmitter.kt`

- [ ] **Step 1: Create the new top-level extension file**

```kotlin
// core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/GoTaintRuleEmit.kt
package org.opentaint.semgrep.pattern.conversion

import org.opentaint.dataflow.configuration.go.serialized.GoSerializedGlobalSource
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep

fun TaintRuleFromSemgrep<GoSerializedItem>.toGoSerializedTaintConfig(): GoSerializedTaintConfig {
    val items = taintRules.flatMap { it.rules }
    return GoSerializedTaintConfig(
        globalSource = items.filterIsInstance<GoSerializedGlobalSource>(),
        source = items.filterIsInstance<GoSerializedRule.Source>(),
        sink = items.filterIsInstance<GoSerializedRule.Sink>(),
        passThrough = items.filterIsInstance<GoSerializedRule.PassThrough>(),
        cleaner = items.filterIsInstance<GoSerializedRule.Cleaner>(),
    )
}

fun TaintRuleFromSemgrep<GoSerializedItem>.toGoTaintConfiguration(): GoTaintConfiguration =
    GoTaintConfiguration().also { it.loadConfig(toGoSerializedTaintConfig()) }
```

- [ ] **Step 2: Delete the test-only emitter class**

```bash
rm /drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-go-querylang/src/test/kotlin/org/opentaint/GoTaintRuleEmitter.kt
```

- [ ] **Step 3: Compile the production main set**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-go-querylang:compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/opentaint-go-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/GoTaintRuleEmit.kt
git add core/opentaint-go-querylang/src/test/kotlin/org/opentaint/GoTaintRuleEmitter.kt
git commit -m "Promote Go semgrep→taint-config emitter to main as top-level extensions"
```

### Task 2: Update test files to use the new extensions

**Files:**
- Modify: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/pattern/conversion/go/GoTaintRuleEmitterTest.kt`
- Modify: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/pattern/GoRuleEmitTest.kt`
- Modify: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoMassiveSampleTest.kt`
- Modify: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt`
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoSemgrepReachabilityTest.kt`

- [ ] **Step 1: Replace `org.opentaint.GoTaintRuleEmitter` import + call in `GoTaintRuleEmitterTest.kt`**

Remove `import org.opentaint.GoTaintRuleEmitter` and add `import org.opentaint.semgrep.pattern.conversion.toGoTaintConfiguration`.

Replace **every** call of the form `GoTaintRuleEmitter().emit(rule)` with `rule.toGoTaintConfiguration()`. There are 7 such calls in this file (`grep -c "GoTaintRuleEmitter()" GoTaintRuleEmitterTest.kt`).

- [ ] **Step 2: Same substitution in `GoRuleEmitTest.kt`**

Remove `import org.opentaint.GoTaintRuleEmitter` and add `import org.opentaint.semgrep.pattern.conversion.toGoTaintConfiguration`.

Replace the single occurrence of `GoTaintRuleEmitter().emit(firstRule)` with `firstRule.toGoTaintConfiguration()`.

- [ ] **Step 3: Same substitution in `GoMassiveSampleTest.kt`**

Remove `import org.opentaint.GoTaintRuleEmitter` and add `import org.opentaint.semgrep.pattern.conversion.toGoTaintConfiguration`.

In the body of `loadConfig`, change

```kotlin
return GoTaintRuleEmitter().emit(typed)
```

to

```kotlin
return typed.toGoTaintConfiguration()
```

- [ ] **Step 4: Same substitution in `GoSampleBasedTest.kt`**

Remove the `org.opentaint.GoTaintRuleEmitter` import. Search for `GoTaintRuleEmitter` in the file and rewrite each call to `xxx.toGoTaintConfiguration()` using the local rule variable. There is also an inner class `private class GoTaintRuleEmitter { ... }` later in the file — delete it; it duplicates the production extension.

- [ ] **Step 5: Same substitution in `GoSemgrepReachabilityTest.kt`**

Same import swap. There is exactly one `GoTaintRuleEmitter().emit(firstRule)` call to rewrite. Verify with:

```bash
grep -n "GoTaintRuleEmitter" core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoSemgrepReachabilityTest.kt
```

Expected: no matches after edits.

- [ ] **Step 6: Compile all touched test sets**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-go-querylang:compileTestKotlin :compileTestKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 7: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add -A core/opentaint-go-querylang/src/test/kotlin core/src/test/kotlin
git commit -m "Switch Go emitter tests to top-level toGoTaintConfiguration extension"
```

### Task 3: Convert `GoTaintRulesProvider` into an interface

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoTaintRulesProvider.kt`

- [ ] **Step 1: Replace the file contents with the interface**

```kotlin
// core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoTaintRulesProvider.kt
package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFunctionSignature

interface GoTaintRulesProvider {
    fun sourceRulesForGlobal(globalName: String): List<TaintRule.GlobalReadSource>
    fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Source>
    fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRule.Sink>
    fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRule.PassThrough>
    fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean = false): List<TaintRule.Cleaner>
}
```

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-dataflow-core:opentaint-go-dataflow:compileKotlin
```

Expected: this **fails** until Task 4 is done, because `GoAnalysisManager` and any other code constructing `GoTaintRulesProvider(configuration)` will no longer compile. Note the failure list — Task 4 fixes it.

- [ ] **Step 3: (Defer commit until Task 4 builds clean)**

### Task 4: `GoTaintConfiguration` implements `GoTaintRulesProvider`; fix call sites

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoTaintConfiguration.kt`
- Any constructor call `GoTaintRulesProvider(configuration)` becomes `configuration` (since `GoTaintConfiguration` now implements the interface).

- [ ] **Step 1: Add interface to `GoTaintConfiguration` and the five delegating methods**

Change the class signature line from

```kotlin
class GoTaintConfiguration {
```

to

```kotlin
class GoTaintConfiguration : GoTaintRulesProvider {
```

Append the following five methods inside the class (place them right after `loadConfig`):

```kotlin
override fun sourceRulesForGlobal(globalName: String): List<TaintRule.GlobalReadSource> =
    sourceForGlobal(globalName)

override fun sourceRulesForCall(
    signature: GoFunctionSignature, allRelevant: Boolean,
): List<TaintRule.Source> = sourceForFunction(signature, allRelevant)

override fun sinkRulesForCall(signature: GoFunctionSignature): List<TaintRule.Sink> =
    sinkForFunction(signature)

override fun passThroughRulesForCall(signature: GoFunctionSignature): List<TaintRule.PassThrough> =
    passThroughForFunction(signature)

override fun cleanerRulesForCall(
    signature: GoFunctionSignature, allRelevant: Boolean,
): List<TaintRule.Cleaner> = cleanerForFunction(signature, allRelevant)
```

- [ ] **Step 2: Find every call site that constructs `GoTaintRulesProvider(...)`**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
grep -rn "GoTaintRulesProvider(" --include='*.kt' core
```

Expected matches (replace each `GoTaintRulesProvider(cfg)` with just `cfg`):

- `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt` — parameter type already accepts the interface; constructor sites in callers may need updating.
- `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoMassiveSampleTest.kt`
- `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/semgrep/GoSampleBasedTest.kt`
- `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoSemgrepReachabilityTest.kt`

For each: replace `GoTaintRulesProvider(config)` with `config` (since `config: GoTaintConfiguration` already satisfies the interface).

- [ ] **Step 3: Compile both targets**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-dataflow-core:opentaint-go-dataflow:compileKotlin :compileKotlin :opentaint-go-querylang:compileTestKotlin :compileTestKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 4: Commit Tasks 3+4 together**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add -A
git commit -m "Promote GoTaintRulesProvider to an interface and let GoTaintConfiguration implement it"
```

### Task 5: Add `GoCombinedTaintRulesProvider`

**Files:**
- Create: `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoCombinedTaintRulesProvider.kt`

- [ ] **Step 1: Write the combined provider**

```kotlin
// core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoCombinedTaintRulesProvider.kt
package org.opentaint.dataflow.go.rules

import org.opentaint.dataflow.go.GoFunctionSignature

class GoCombinedTaintRulesProvider(
    private val base: GoTaintRulesProvider,
    private val combined: GoTaintRulesProvider,
    private val options: CombinationOptions = CombinationOptions(),
) : GoTaintRulesProvider {
    enum class CombinationMode { EXTEND, OVERRIDE, IGNORE }

    data class CombinationOptions(
        val source: CombinationMode = CombinationMode.OVERRIDE,
        val sink: CombinationMode = CombinationMode.OVERRIDE,
        val passThrough: CombinationMode = CombinationMode.EXTEND,
        val cleaner: CombinationMode = CombinationMode.EXTEND,
        val globalSource: CombinationMode = CombinationMode.OVERRIDE,
    )

    override fun sourceRulesForGlobal(globalName: String) =
        combine(options.globalSource,
            base.sourceRulesForGlobal(globalName),
            combined.sourceRulesForGlobal(globalName))

    override fun sourceRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean) =
        combine(options.source,
            base.sourceRulesForCall(signature, allRelevant),
            combined.sourceRulesForCall(signature, allRelevant))

    override fun sinkRulesForCall(signature: GoFunctionSignature) =
        combine(options.sink,
            base.sinkRulesForCall(signature),
            combined.sinkRulesForCall(signature))

    override fun passThroughRulesForCall(signature: GoFunctionSignature) =
        combine(options.passThrough,
            base.passThroughRulesForCall(signature),
            combined.passThroughRulesForCall(signature))

    override fun cleanerRulesForCall(signature: GoFunctionSignature, allRelevant: Boolean) =
        combine(options.cleaner,
            base.cleanerRulesForCall(signature, allRelevant),
            combined.cleanerRulesForCall(signature, allRelevant))

    private fun <T> combine(mode: CombinationMode, base: List<T>, extra: List<T>): List<T> = when (mode) {
        CombinationMode.EXTEND -> base + extra
        CombinationMode.OVERRIDE -> extra.takeIf { it.isNotEmpty() } ?: base
        CombinationMode.IGNORE -> base
    }
}
```

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-dataflow-core:opentaint-go-dataflow:compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/rules/GoCombinedTaintRulesProvider.kt
git commit -m "Add GoCombinedTaintRulesProvider for base/user-approximation merging"
```

### Task 6: Expose `loadGoSerializedTaintConfig` from `GoConfigLoader`

**Files:**
- Modify: `core/opentaint-config/go-config/src/main/kotlin/org/opentaint/go/config/GoConfigLoader.kt`

- [ ] **Step 1: Rename and expose the parser**

At the bottom of `GoConfigLoader.kt`, add a public top-level function that reuses the same YAML parsing as the existing internal loader:

```kotlin
fun loadGoSerializedTaintConfig(stream: java.io.InputStream): GoSerializedTaintConfig {
    val passThrough = parsePassThroughRules(stream)
    return GoSerializedTaintConfig(passThrough = passThrough)
}
```

Then change the visibility of the existing `private fun parsePassThroughRules(stream: InputStream)` to `internal fun parsePassThroughRules(stream: InputStream)` so the new function can call it. (Both live in the same file, so `internal` suffices.)

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-config:go-config:compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/opentaint-config/go-config/src/main/kotlin/org/opentaint/go/config/GoConfigLoader.kt
git commit -m "Expose loadGoSerializedTaintConfig for external approximation YAMLs"
```

---

## Phase 2 — Shared options refactor

### Task 7: Create `CommonAnalysisOptions`

**Files:**
- Create: `core/src/main/kotlin/org/opentaint/jvm/sast/project/CommonAnalysisOptions.kt`

- [ ] **Step 1: Write the data class**

```kotlin
// core/src/main/kotlin/org/opentaint/jvm/sast/project/CommonAnalysisOptions.kt
package org.opentaint.jvm.sast.project

import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.jvm.sast.dataflow.DebugOptions
import java.nio.file.Path
import kotlin.time.Duration

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

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/jvm/sast/project/CommonAnalysisOptions.kt
git commit -m "Introduce CommonAnalysisOptions data class for Java+Go sharing"
```

### Task 8: Refactor `ProjectAnalysisOptions` to compose `CommonAnalysisOptions`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisOptions.kt`
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalyzer.kt`
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/LoadSemgrepRules.kt`
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/runner/ProjectAnalyzerRunner.kt`
- Modify: every other reader of the migrated fields (find via grep below)

- [ ] **Step 1: Rewrite `ProjectAnalysisOptions`**

```kotlin
// core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisOptions.kt
package org.opentaint.jvm.sast.project

import org.opentaint.jvm.sast.dataflow.DataFlowApproximationLoader
import org.opentaint.jvm.sast.dataflow.TaintAnalyzerOptions

data class ProjectAnalysisOptions(
    val common: CommonAnalysisOptions = CommonAnalysisOptions(),
    val cwe: List<Int> = emptyList(),
    val useSymbolicExecution: Boolean = false,
    val symbolicExecutionTimeout: kotlin.time.Duration = kotlin.time.Duration.ZERO,
    val projectKind: ProjectKind = ProjectKind.UNKNOWN,
    val storeSummaries: Boolean = false,
    val experimentalAAInterProcCallDepth: Int = 1,
    val approximationOptions: DataFlowApproximationLoader.Options = DataFlowApproximationLoader.Options(),
) {
    val summariesApMode get() = common.ifdsApMode.takeIf { storeSummaries }

    fun taintAnalyzerOptions() = TaintAnalyzerOptions(
        ifdsTimeout = common.ifdsAnalysisTimeout,
        ifdsApMode = common.ifdsApMode,
        symbolicExecutionEnabled = useSymbolicExecution,
        analysisCwe = cwe.takeIf { it.isNotEmpty() }?.toSet(),
        storeSummaries = storeSummaries,
        experimentalAAInterProcCallDepth = experimentalAAInterProcCallDepth,
        debugOptions = common.debugOptions,
    )
}
```

- [ ] **Step 2: Grep for every removed field and rewrite call sites**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
for f in customApproximationConfig semgrepRuleSet semgrepRuleLoadTrace semgrepSeverity semgrepRuleId trackExternalMethods ifdsAnalysisTimeout ifdsApMode debugOptions sarifGenerationOptions; do
  grep -rn "options.$f" --include='*.kt' core | grep -v "options.common.$f"
done
```

For every match in production code, change `options.<field>` to `options.common.<field>`. Skip strict references inside `ProjectAnalysisOptions` itself.

Hot spots that must be updated (initial list — confirm by grep):

- `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalyzer.kt` — reads `options.customApproximationConfig`, `options.taintAnalyzerOptions()`, `options.semgrepRuleLoadTrace`, `options.trackExternalMethods`, `options.debugOptions`, `options.sarifGenerationOptions`, `options.useSymbolicExecution`, `options.symbolicExecutionTimeout`, `options.experimentalAAInterProcCallDepth`. JVM-only fields stay; shared ones move under `.common`.
- `core/src/main/kotlin/org/opentaint/jvm/sast/project/TestProjectAnalyzer.kt` — same rewrite as above (mirror copy/paste).
- `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/LoadSemgrepRules.kt` — see Task 9 (moves to `CommonAnalysisOptions`).
- `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisContext.kt` — if it reads any shared field, redirect via `.common`.
- `core/src/main/kotlin/org/opentaint/jvm/sast/runner/ProjectAnalyzerRunner.kt` — the constructor call to `ProjectAnalysisOptions(...)`. Rewrite as:

```kotlin
val options = ProjectAnalysisOptions(
    common = CommonAnalysisOptions(
        customApproximationConfig = approximationsConfig,
        semgrepRuleSet = semgrepRuleSet,
        semgrepRuleLoadTrace = semgrepRuleLoadTrace,
        semgrepSeverity = semgrepRuleSeverity,
        semgrepRuleId = semgrepRuleId,
        trackExternalMethods = trackExternalMethods,
        ifdsAnalysisTimeout = ifdsAnalysisTimeout.seconds,
        ifdsApMode = ifdsApMode,
        debugOptions = debugOptions,
        sarifGenerationOptions = sarifOptions,
    ),
    cwe = cwe,
    useSymbolicExecution = useSymbolicExecution,
    symbolicExecutionTimeout = symbolicExecutionTimeout.seconds,
    projectKind = projectKind,
    storeSummaries = false,
    experimentalAAInterProcCallDepth = experimentalAAInterProcCallDepth,
    approximationOptions = DataFlowApproximationLoader.Options(
        customApproximationPaths = dataflowApproximations,
    ),
)
```

- [ ] **Step 3: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin :compileTestKotlin
```

Expected: BUILD SUCCESSFUL. If a compile error references an un-migrated `options.<field>`, fix it then re-run.

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add -A
git commit -m "Compose ProjectAnalysisOptions over CommonAnalysisOptions; redirect call sites"
```

### Task 9: Make `loadSemgrepRules` polymorphic over the language strategy

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/LoadSemgrepRules.kt`
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalyzer.kt` (call site)

- [ ] **Step 1: Rewrite `LoadSemgrepRules.kt`**

```kotlin
// core/src/main/kotlin/org/opentaint/jvm/sast/project/rules/LoadSemgrepRules.kt
package org.opentaint.jvm.sast.project.rules

import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import mu.KLogging
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.jvm.sast.project.CommonAnalysisOptions
import org.opentaint.semgrep.pattern.LanguageStrategy
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import java.nio.file.Path
import kotlin.io.path.extension
import kotlin.io.path.outputStream
import kotlin.io.path.readText
import kotlin.io.path.relativeTo
import kotlin.io.path.walk

private val logger = object : KLogging() {}.logger

fun CommonAnalysisOptions.loadSemgrepRules(strategy: LanguageStrategy<*, *>): SemgrepRuleLoader.RuleLoadResult {
    val trace = SemgrepLoadTrace()
    val rules = parseSemgrepRules(strategy, semgrepRuleSet, semgrepSeverity, semgrepRuleId, trace)
    semgrepRuleLoadTrace?.let { writeTrace(it, trace) }
    return rules
}

private fun writeTrace(traceFile: Path, trace: SemgrepLoadTrace) {
    val compressed = trace.compressed()
    runCatching {
        val pretty = Json { prettyPrint = true }
        traceFile.outputStream().bufferedWriter().use { it.write(pretty.encodeToString(compressed)) }
        logger.info { "Wrote semgrep load trace to $traceFile" }
    }.onFailure { logger.error(it) { "Failed to write semgrep load trace to $traceFile: ${it.message}" } }
}

private fun parseSemgrepRules(
    strategy: LanguageStrategy<*, *>,
    rulesPath: List<Path>,
    severity: List<Severity>,
    ruleId: List<String>,
    semgrepTrace: SemgrepLoadTrace,
): SemgrepRuleLoader.RuleLoadResult {
    val loader = SemgrepRuleLoader(listOf(strategy))
    val ruleExt = arrayOf("yaml", "yml")
    for (rulesRoot in rulesPath) {
        rulesRoot.walk().filter { it.extension in ruleExt }.forEach { rulePath ->
            val rel = rulePath.relativeTo(rulesRoot)
            loader.registerRuleSet(rulePath.readText(), rel, rulesRoot, semgrepTrace)
        }
    }
    val loaded = loader.loadRules(severity, ruleId)
    logger.info { "Total loaded ${loaded.rulesWithMeta.sumOf { it.first.size }} rules" }
    return loaded
}
```

Note the `LanguageStrategy<*, *>` import: it lives in
`org.opentaint.semgrep.pattern.conversion.LanguageStrategy` (the existing
sealed/interface base for `JavaLanguageStrategy` and `GoLanguageStrategy`).
If your IDE picks a different import, fix manually. Run

```bash
grep -rn "interface LanguageStrategy\|class LanguageStrategy" core/opentaint-java-querylang/src/main core/opentaint-go-querylang/src/main
```

to confirm the FQN.

- [ ] **Step 2: Update the only caller in `ProjectAnalyzer.preloadRules`**

Change

```kotlin
val loadedRules = options.loadSemgrepRules()
```

to

```kotlin
val loadedRules = options.common.loadSemgrepRules(JavaLanguageStrategy())
```

Add `import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy`.

- [ ] **Step 3: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add -A
git commit -m "Make loadSemgrepRules polymorphic over LanguageStrategy"
```

---

## Phase 3 — Go analyzer wiring

### Task 10: Create `GoProjectAnalysisOptions`

**Files:**
- Create: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalysisOptions.kt`

- [ ] **Step 1: Write the options class**

```kotlin
// core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalysisOptions.kt
package org.opentaint.go.sast.project

import org.opentaint.jvm.sast.project.CommonAnalysisOptions

data class GoProjectAnalysisOptions(
    val common: CommonAnalysisOptions = CommonAnalysisOptions(),
)
```

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalysisOptions.kt
git commit -m "Add GoProjectAnalysisOptions composed over CommonAnalysisOptions"
```

### Task 11: Thread `ExternalMethodTracker` through `GoTaintAnalyzer`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt`

- [ ] **Step 1: Add the optional tracker parameter and forward it**

Replace the file's constructor block and `analyzeWithIfds` so the tracker is plumbed through:

```kotlin
class GoTaintAnalyzer(
    private val cp: GoIRProgram,
    private val taintConfig: GoTaintRulesProvider,
    private val unitResolver: UnitResolver<GoIRFunction>,
    private val externalMethodTracker: ExternalMethodTracker? = null,
    private val analysisTimeout: Duration = 1.minutes,
    private val cancellationTimeout: Duration = 10.seconds,
) {
    @Suppress("UNCHECKED_CAST")
    fun analyzeWithIfds(entryPoints: List<GoIRFunction>): List<VulnerabilityWithTrace> {
        val ifdsGraph = GoApplicationGraph(cp, unitResolver)

        val engine = TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(cp, taintConfig, externalMethodTracker = externalMethodTracker),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = unitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethods = entryPoints.map { MethodWithContext(it, EmptyMethodContext) }
        return engine.use { eng ->
            eng.runAnalysis(startMethods, timeout = analysisTimeout, cancellationTimeout = cancellationTimeout)
            val vulnerabilities = eng.getVulnerabilities()
            eng.resolveVulnerabilityTraces(
                entryPoints.toSet(), vulnerabilities,
                resolverParams = TraceResolver.Params(),
                timeout = analysisTimeout, cancellationTimeout = cancellationTimeout,
            ).filter { it.trace != null }
        }
    }
}
```

Add the missing import: `import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker`.

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt
git commit -m "Thread ExternalMethodTracker through GoTaintAnalyzer"
```

### Task 12: Implement `GoProjectAnalyzer`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt`

- [ ] **Step 1: Replace the file with the full implementation**

```kotlin
// core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt
package org.opentaint.go.sast.project

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.encodeToStream
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ap.ifds.taint.SkippedExternalMethods
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.rules.GoCombinedTaintRulesProvider
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.rules.GoTaintRulesProvider
import org.opentaint.go.config.GoConfigLoader
import org.opentaint.go.config.loadGoSerializedTaintConfig
import org.opentaint.go.sast.dataflow.GoTaintAnalyzer
import org.opentaint.go.sast.dataflow.GoUnitResolver
import org.opentaint.go.sast.sarif.GoSarifGenerator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.jvm.sast.project.ProjectAnalysisStatus
import org.opentaint.jvm.sast.project.rules.loadSemgrepRules
import org.opentaint.project.GoProject
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.toGoSerializedTaintConfig
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.inputStream
import kotlin.io.path.outputStream

class GoProjectAnalyzer(
    private val project: GoProject,
    private val resultDir: Path,
    private val options: GoProjectAnalysisOptions = GoProjectAnalysisOptions(),
) {
    fun analyze(): ProjectAnalysisStatus = try {
        GoIRClient().use { client ->
            logger.info { "Building Go IR for project: ${project.projectDir}" }
            val cp = client.buildFromDir(project.projectDir, "./...")

            val rulesProvider = loadRules()
            val tracker = if (options.common.trackExternalMethods) ExternalMethodTracker() else null

            val analyzer = GoTaintAnalyzer(
                cp = cp,
                taintConfig = rulesProvider,
                unitResolver = GoUnitResolver(cp.packages.keys.toSet()),
                externalMethodTracker = tracker,
            )
            val entryPoints = selectEntryPoints(cp)
            logger.info { "Selected ${entryPoints.size} Go entry points" }

            val traces = analyzer.analyzeWithIfds(entryPoints)
            logger.info { "Go analysis produced ${traces.size} traces" }

            writeReport(traces)
            tracker?.let { writeExternalMethodsYaml(it.getExternalMethods()) }
        }
        ProjectAnalysisStatus.OK
    } catch (ex: Throwable) {
        logger.error(ex) { "Go analysis failed for project: ${project.projectDir}" }
        ProjectAnalysisStatus.EXCEPTION
    }

    private fun loadRules(): GoTaintRulesProvider {
        val userConfig = GoTaintConfiguration()

        GoConfigLoader.getConfig()?.let { userConfig.loadConfig(it) }

        val semgrepRules = options.common.loadSemgrepRules(GoLanguageStrategy())
        for ((rule, _) in semgrepRules.rulesWithMeta) {
            @Suppress("UNCHECKED_CAST")
            val typed = rule as TaintRuleFromSemgrep<GoSerializedItem>
            userConfig.loadConfig(typed.toGoSerializedTaintConfig())
        }

        if (options.common.customApproximationConfig.isEmpty()) return userConfig

        val approxConfig = GoTaintConfiguration()
        options.common.customApproximationConfig.forEach { cfg ->
            cfg.inputStream().use { approxConfig.loadConfig(loadGoSerializedTaintConfig(it)) }
        }
        return GoCombinedTaintRulesProvider(userConfig, approxConfig)
    }

    private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
        cp.allFunctions().filter { it.hasBody && it.pkg != null && !it.isSynthetic && it.parent == null }

    private fun writeReport(traces: List<VulnerabilityWithTrace>) {
        val sarif = options.common.sarifGenerationOptions
        val generator = GoSarifGenerator(sarif, project.projectDir)
        (resultDir / sarif.sarifFileName).outputStream().use { out ->
            generator.generateSarif(out, traces.asSequence())
        }
        logger.info { "Wrote Go SARIF report to ${resultDir / sarif.sarifFileName}" }
    }

    private fun writeExternalMethodsYaml(methods: SkippedExternalMethods) {
        val yaml = Yaml(configuration = YamlConfiguration(encodeDefaults = true))
        (resultDir / "external-methods-without-rules.yaml").outputStream().use {
            yaml.encodeToStream(methods.withoutRules, it)
        }
        (resultDir / "external-methods-with-rules.yaml").outputStream().use {
            yaml.encodeToStream(methods.withRules, it)
        }
        logger.info {
            "Wrote external-methods YAMLs (${methods.withoutRules.size} without rules, " +
                "${methods.withRules.size} with rules)"
        }
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}
```

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: BUILD SUCCESSFUL. If the import `org.opentaint.go.config.loadGoSerializedTaintConfig` fails, double-check that Task 6 declared it at the top-level (not inside a companion). If `ProjectAnalysisStatus` import fails, confirm its FQN with `grep -n "class ProjectAnalysisStatus\|enum class ProjectAnalysisStatus" core/src/main/kotlin/org/opentaint/jvm/sast/project/ProjectAnalysisStatus.kt`.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt
git commit -m "Implement GoProjectAnalyzer with semgrep + bundled config + approximations"
```

---

## Phase 4 — Runner dispatch

### Task 13: Add abstract `analyzeGoProject` and Go dispatch in `AbstractAnalyzerRunner`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/runner/AbstractAnalyzerRunner.kt`

- [ ] **Step 1: Replace the Go fold loop with real dispatch and add the abstract method**

In `main()`, replace

```kotlin
val status = resolvedProject.goProjects.fold(javaStatus) { acc, gp ->
    logger.warn { "Go project analysis is not implemented: ${gp.projectDir}" }
    acc
}
```

with

```kotlin
val status = resolvedProject.goProjects.fold(javaStatus) { acc, gp ->
    maxOf(acc, runGoProjectAnalysis(gp))
}
```

Then add the helper next to `runProjectAnalysisRecursively`:

```kotlin
private fun runGoProjectAnalysis(project: GoProject): ProjectAnalysisStatus = try {
    logger.info { "Start Go analysis for project: ${project.projectDir}" }
    analyzeGoProject(project, outputDir, debugOptions).also {
        logger.info { "Finish Go analysis for project: ${project.projectDir}" }
    }
} catch (ex: Throwable) {
    logger.error(ex) { "Fail Go analysis for project: ${project.projectDir}" }
    ProjectAnalysisStatus.EXCEPTION
}
```

Then add the abstract method next to `analyzeProject`:

```kotlin
protected abstract fun analyzeGoProject(project: GoProject, analyzerOutputDir: Path, debugOptions: DebugOptions): ProjectAnalysisStatus
```

`outputDir` is currently `private`; promote it to `protected` so the helper inside the abstract class can read it (it already does via the captured closure, so no change needed if you keep `runGoProjectAnalysis` as a non-extension method inside the same class — but verify the existing Java helper compiles in the same scope).

Add `import org.opentaint.project.GoProject`.

- [ ] **Step 2: Compile (expect the runner to fail until Task 14)**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: fails with "Class 'ProjectAnalyzerRunner' is not abstract and does not implement abstract member analyzeGoProject". Task 14 fixes this.

### Task 14: Implement `analyzeGoProject` in `ProjectAnalyzerRunner`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/jvm/sast/runner/ProjectAnalyzerRunner.kt`

- [ ] **Step 1: Add the override**

Add inside the class, near `analyzeProject`:

```kotlin
override fun analyzeGoProject(
    project: GoProject,
    analyzerOutputDir: Path,
    debugOptions: DebugOptions,
): ProjectAnalysisStatus {
    val sarifOptions = SarifGenerationOptions(
        sarifFileName = sarifFileName,
        sarifCodeFlowLimit = sarifCodeFlowLimit,
        useSemgrepStyleId = sarifSemgrepStyleId,
        toolVersion = sarifToolVersion,
        toolSemanticVersion = sarifToolSemanticVersion,
        uriBase = sarifUriBase,
        generateFingerprint = sarifGenerateFingerprint,
    )

    val options = GoProjectAnalysisOptions(
        common = CommonAnalysisOptions(
            customApproximationConfig = approximationsConfig,
            semgrepRuleSet = semgrepRuleSet,
            semgrepRuleLoadTrace = semgrepRuleLoadTrace,
            semgrepSeverity = semgrepRuleSeverity,
            semgrepRuleId = semgrepRuleId,
            trackExternalMethods = trackExternalMethods,
            ifdsAnalysisTimeout = ifdsAnalysisTimeout.seconds,
            ifdsApMode = ifdsApMode,
            debugOptions = debugOptions,
            sarifGenerationOptions = sarifOptions,
        ),
    )

    return GoProjectAnalyzer(project, analyzerOutputDir, options).analyze()
}
```

Add the missing imports:

```kotlin
import org.opentaint.go.sast.project.GoProjectAnalysisOptions
import org.opentaint.go.sast.project.GoProjectAnalyzer
import org.opentaint.jvm.sast.project.CommonAnalysisOptions
import org.opentaint.project.GoProject
```

- [ ] **Step 2: Compile and run unit tests for the runner**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin :compileTestKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 3: Commit Tasks 13+14**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add -A
git commit -m "Dispatch GoProject analysis through AbstractAnalyzerRunner + ProjectAnalyzerRunner"
```

---

## Phase 5 — Autobuilder

### Task 15: Detect `go.mod` directories in `ProjectAutoBuilder`

**Files:**
- Modify: `core/opentaint-jvm-autobuilder/src/main/kotlin/org/opentaint/project/ProjectAutoBuilder.kt`

- [ ] **Step 1: Add Go scan and wire it into the resulting `Project`**

After the existing `ProjectResolver.resolveProject(...)` call, add:

```kotlin
val goProjects = findGoProjects(projectRootDir)
logger.info { "Detected ${goProjects.size} Go modules" }
```

And rewrite the `topLevelProject` construction to use `goProjects` instead of `emptyList()`:

```kotlin
val topLevelProject = Project(
    projectRoot = projectRootDir,
    goProjects = goProjects,
    javaProjects = Project.flattenJavaProject(resolvedProject),
)
```

But `resolvedProject` may be `null` when only Go modules exist. Handle that:

```kotlin
val resolvedProject = when (val b = buildType) {
    is BuildProject -> ProjectResolver.resolveProject(projectRootDir, resolverWorkDir)
    is ProjectFromCP -> ProjectFromCPResolver().resolveProject(projectRootDir, resolverWorkDir, b)
}
val javaProjects = resolvedProject?.let { Project.flattenJavaProject(it) }.orEmpty()
val goProjects = findGoProjects(projectRootDir)
if (javaProjects.isEmpty() && goProjects.isEmpty()) {
    logger.error { "No projects (java or go) resolved at $projectRootDir" }
    return
}

val topLevelProject = Project(
    projectRoot = projectRootDir,
    goProjects = goProjects,
    javaProjects = javaProjects,
)
```

The `PortableProjectBuild` branch keeps using `resolvedProject` for Java packaging; if it's `null` (Go-only), call `topLevelProject.dump(...)` regardless and skip the portable creator for Go-only projects:

```kotlin
when (val b = build) {
    is SimpleProjectBuild -> topLevelProject.dump(b.result.createParentDirectories())
    is PortableProjectBuild -> {
        if (resolvedProject == null) {
            topLevelProject.dump((b.resultDir / "project.yaml").createParentDirectories())
        } else {
            PortableProjectCreator(b.resultDir, resolvedProject).create()
        }
    }
}
```

Add `findGoProjects` at the bottom of the file (top-level):

```kotlin
private val logger = object : KLogging() {}.logger

private fun findGoProjects(root: Path): List<GoProject> {
    if (!root.toFile().isDirectory) return emptyList()
    val out = mutableListOf<GoProject>()
    root.visitFileTree {
        onPreVisitDirectory { dir, _ ->
            when {
                dir.isHiddenSubDirOf(root) -> java.nio.file.FileVisitResult.SKIP_SUBTREE
                (dir / "go.mod").toFile().isFile -> {
                    out += GoProject(projectDir = dir)
                    java.nio.file.FileVisitResult.SKIP_SUBTREE
                }
                else -> java.nio.file.FileVisitResult.CONTINUE
            }
        }
    }
    return out
}
```

(Move the existing `logger` if duplicated.)

Add imports:

```kotlin
import org.opentaint.project.GoProject
import kotlin.io.path.div
import kotlin.io.path.visitFileTree
```

- [ ] **Step 2: Add a small unit test**

Create `core/opentaint-jvm-autobuilder/src/test/kotlin/org/opentaint/project/FindGoProjectsTest.kt`:

```kotlin
package org.opentaint.project

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.io.TempDir
import java.nio.file.Path
import kotlin.io.path.createDirectories
import kotlin.io.path.writeText
import kotlin.test.assertEquals

class FindGoProjectsTest {
    @Test
    fun `detects top-level go.mod`(@TempDir root: Path) {
        (root.resolve("go.mod")).writeText("module example.com/main\n")
        val result = findGoProjectsForTest(root)
        assertEquals(listOf(root), result.map { it.projectDir })
    }

    @Test
    fun `stops descent at nested go.mod`(@TempDir root: Path) {
        (root.resolve("go.mod")).writeText("module example.com/main\n")
        val sub = root.resolve("sub").createDirectories()
        (sub.resolve("go.mod")).writeText("module example.com/sub\n")
        val result = findGoProjectsForTest(root)
        assertEquals(listOf(root), result.map { it.projectDir })
    }

    @Test
    fun `picks up sibling Go modules under a non-Go parent`(@TempDir root: Path) {
        val a = root.resolve("a").createDirectories().also { (it.resolve("go.mod")).writeText("module a\n") }
        val b = root.resolve("b").createDirectories().also { (it.resolve("go.mod")).writeText("module b\n") }
        val result = findGoProjectsForTest(root).map { it.projectDir }.sortedBy { it.fileName.toString() }
        assertEquals(listOf(a, b), result)
    }
}
```

Then promote `findGoProjects` to internal visibility (`internal fun findGoProjects(...)`), and add a thin alias for tests:

```kotlin
// in ProjectAutoBuilder.kt
internal fun findGoProjectsForTest(root: Path): List<GoProject> = findGoProjects(root)
```

- [ ] **Step 3: Compile and run the new test**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-jvm-autobuilder:compileKotlin :opentaint-jvm-autobuilder:test --tests "org.opentaint.project.FindGoProjectsTest"
```

Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add -A
git commit -m "Auto-detect Go modules (go.mod) in ProjectAutoBuilder"
```

---

## Phase 6 — Build config

### Task 16: Promote dependencies in `core/build.gradle.kts`

**Files:**
- Modify: `core/build.gradle.kts`

- [ ] **Step 1: Change the dependency scope**

Replace the line

```kotlin
testImplementation(project(":opentaint-go-querylang"))
```

with

```kotlin
implementation(project(":opentaint-go-querylang"))
implementation("org.opentaint.config:go-config")
```

Confirm the surrounding block still compiles after this change:

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

- [ ] **Step 2: Smoke-build the analyzer fat jar (this is the artifact opentaint will consume)**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :projectAnalyzerJar
ls -la build/libs/opentaint-project-analyzer-all.jar
```

Expected: jar exists.

- [ ] **Step 3: Smoke-build the autobuilder fat jar**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-jvm-autobuilder:projectAutoBuilderJar
ls -la opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder-all.jar
```

Expected: jar exists.

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/build.gradle.kts
git commit -m "Promote Go querylang + go-config to runtime implementation deps"
```

---

## Phase 7 — Wired-build verification

### Task 17: Sanity-check the refactor

- [ ] **Step 1: Run the full test suite for `core` and `opentaint-go-querylang`**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :test :opentaint-go-querylang:test 2>&1 | tee /tmp/gomassive-before.log
grep -E "tests completed|FAILED" /tmp/gomassive-before.log | tail -5
```

Expected: the **existing** failing tests in `GoMassiveSampleTest` are still 27; no new failures elsewhere. If the count changes, investigate before continuing.

- [ ] **Step 2: Smoke-run the analyzer on one Go sample**

Pick a small one — `cmdinj_01_env_basic`:

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
SAMPLES=opentaint-go-querylang/samples-go-massive/cmdinj_01_env_basic
mkdir -p /tmp/go-smoke
# create a one-line Go-only project model by hand
cat > /tmp/go-smoke/project.yaml <<EOF
projectRoot: $SAMPLES
goProjects:
  - projectDir: $SAMPLES
javaProjects: []
EOF
./gradlew :runProjectAnalyzer --args "--project /tmp/go-smoke/project.yaml --output-dir /tmp/go-smoke/results --semgrep-rule-set $SAMPLES --track-external-methods"
ls /tmp/go-smoke/results
```

Expected: `report-ifds.sarif`, `external-methods-without-rules.yaml`, `external-methods-with-rules.yaml`. The SARIF should be a valid (possibly empty) document; YAMLs may be empty.

- [ ] **Step 3: Commit any cleanup the smoke run revealed**

If the smoke run uncovered an exception (e.g., missing import, NPE), fix it and commit with a descriptive message before moving on.

---

## Phase 8 — Benchmark verification

### Task 18: Clone benchmarks and build project models

- [ ] **Step 1: Clone both benchmarks**

```bash
mkdir -p /drive-testcomp/opentaint-go-rules/benchmarks
cd /drive-testcomp/opentaint-go-rules/benchmarks
git clone https://github.com/flawgarden/go-owasp-converted-mutated.git
git clone https://github.com/flawgarden/go-sec-code-mutated.git
ls go-owasp-converted-mutated/truth.sarif go-sec-code-mutated/truth.sarif
```

Expected: both clones succeed and `truth.sarif` exists in each repo's root.

- [ ] **Step 2: Build project models with the locally built jars**

```bash
ANALYZER_JAR=/drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer-all.jar
AUTOBUILDER_JAR=/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder-all.jar

for bench in go-owasp-converted-mutated go-sec-code-mutated; do
  cd /drive-testcomp/opentaint-go-rules/benchmarks/$bench
  rm -rf .opentaint
  opentaint --experimental compile . \
    --analyzer-jar "$ANALYZER_JAR" \
    --autobuilder-jar "$AUTOBUILDER_JAR" \
    -o .opentaint/project
done
ls /drive-testcomp/opentaint-go-rules/benchmarks/go-owasp-converted-mutated/.opentaint/project/project.yaml
ls /drive-testcomp/opentaint-go-rules/benchmarks/go-sec-code-mutated/.opentaint/project/project.yaml
```

Expected: both project.yaml files contain non-empty `goProjects:` lists.

### Task 19: Run baseline scans

- [ ] **Step 1: Scan each benchmark with built-in rules only**

```bash
ANALYZER_JAR=/drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer-all.jar
AUTOBUILDER_JAR=/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder-all.jar

for bench in go-owasp-converted-mutated go-sec-code-mutated; do
  cd /drive-testcomp/opentaint-go-rules/benchmarks/$bench
  mkdir -p .opentaint/results
  opentaint --experimental scan \
    --project-model .opentaint/project \
    --analyzer-jar "$ANALYZER_JAR" \
    --autobuilder-jar "$AUTOBUILDER_JAR" \
    -o .opentaint/results/baseline.sarif \
    --ruleset builtin \
    --track-external-methods
  echo "=== $bench baseline summary ==="
  opentaint summary .opentaint/results/baseline.sarif --show-findings | head -30
done
```

Expected: the command completes for both benchmarks. With no Go rules in `builtin`, expected findings count is 0 — that's fine. The success criterion at this phase is **the pipeline runs end-to-end**, not the result quality.

- [ ] **Step 2: Sanity-check the SARIF and external-methods YAMLs**

```bash
for bench in go-owasp-converted-mutated go-sec-code-mutated; do
  cd /drive-testcomp/opentaint-go-rules/benchmarks/$bench
  echo "=== $bench files ==="
  ls -la .opentaint/results
  head -5 .opentaint/results/external-methods-without-rules.yaml
done
```

Expected: all three files exist for each benchmark; `external-methods-without-rules.yaml` is populated (real Go projects will call into stdlib/external modules).

### Task 20: TP/FP measurement script and baseline comparison

- [ ] **Step 1: Write a comparison helper**

Save this to `/drive-testcomp/opentaint-go-rules/benchmarks/compare.py`:

```python
#!/usr/bin/env python3
"""Compare a benchmark SARIF against truth.sarif.

Truth conventions (per task description):
  kind=pass  -> the truth says "this should NOT be reported" (FP territory)
  kind=fail  -> the truth says "this is a real bug" (TP territory)

A finding is matched on (artifact_uri, start_line) tuples.
"""
import json, sys, pathlib

def load_locations(path):
    data = json.loads(pathlib.Path(path).read_text())
    locs = []
    for run in data.get("runs", []):
        for result in run.get("results", []):
            kind = result.get("kind", "fail")
            for loc in result.get("locations", []) or []:
                pl = loc.get("physicalLocation", {})
                uri = pl.get("artifactLocation", {}).get("uri", "")
                line = pl.get("region", {}).get("startLine", -1)
                locs.append((uri, line, kind))
    return locs

def main(report, truth):
    rep = load_locations(report)
    tru = load_locations(truth)
    rep_keys = {(uri, line) for uri, line, _ in rep}
    tru_pass = {(uri, line) for uri, line, k in tru if k == "pass"}
    tru_fail = {(uri, line) for uri, line, k in tru if k == "fail"}

    tp = len(rep_keys & tru_fail)
    fp = len(rep_keys & tru_pass)
    missed = len(tru_fail - rep_keys)

    print(f"truth fail (real bugs)  : {len(tru_fail)}")
    print(f"truth pass (decoys)     : {len(tru_pass)}")
    print(f"report findings         : {len(rep_keys)}")
    print(f"TP (report ∩ truth fail): {tp}")
    print(f"FP (report ∩ truth pass): {fp}")
    print(f"FN (truth fail - report): {missed}")
    if len(tru_fail):
        pct = 100.0 * tp / len(tru_fail)
        print(f"TP%                     : {pct:.1f}%")

if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
```

```bash
chmod +x /drive-testcomp/opentaint-go-rules/benchmarks/compare.py
```

- [ ] **Step 2: Compare each baseline**

```bash
for bench in go-owasp-converted-mutated go-sec-code-mutated; do
  echo "=== $bench ==="
  /drive-testcomp/opentaint-go-rules/benchmarks/compare.py \
    /drive-testcomp/opentaint-go-rules/benchmarks/$bench/.opentaint/results/baseline.sarif \
    /drive-testcomp/opentaint-go-rules/benchmarks/$bench/truth.sarif
done
```

Expected: TP% will be ~0% at baseline — confirms the script works and the pipeline is wired. No rules exist to fire yet.

- [ ] **Step 3: Commit the comparison script**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks
git init -q && git add compare.py && git commit -q -m "Add benchmark TP/FP comparison helper"
```

(Optional — the benchmarks dir is outside the main repo; this `git init` keeps the helper versioned alongside the clones if desired.)

---

## End of wiring phase

After Phase 8 completes successfully:

1. The opentaint CLI invokes the locally built analyzer and autobuilder.
2. Go modules are auto-detected from `go.mod`.
3. `GoProjectAnalyzer` runs end-to-end and produces SARIF + external-methods YAMLs.
4. Baseline TP/FP measurement is in place.

**Next action**: invoke `superpowers:brainstorming` for the rule-development phase (per the spec). Rule authoring is not part of this plan.

---

## Self-review notes

- Spec coverage: every section ("Shared options", "GoTaintRulesProvider becomes an interface", "Rule loading", "Analyzer wiring", "Runner dispatch", "Autobuilder Go support", "Module dependency changes", "Wiring the modified jars", "Benchmark verification phase", "Second brainstorming round before rule development") has at least one corresponding Task above. The second-brainstorming-round handoff is the closing note.
- No placeholders, no "TBD"/"similar to Task N"; code blocks contain runnable content.
- Type consistency: provider methods (`sourceRulesForGlobal`, `sourceRulesForCall`, etc.) keep the same signature across the interface, the impl in `GoTaintConfiguration`, the combiner, and the analyzer; `CommonAnalysisOptions` field names stay identical to the JVM ones they replace.

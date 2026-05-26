# Go UnitResolver + Entry-Point Filter Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Plumb the SSA server's `is_stdlib` / `is_dependency` package flags into `GoIRPackage`, simplify `GoUnitResolver` to use them, and tighten `GoProjectAnalyzer.selectEntryPoints` to iterate project packages directly.

**Architecture:** The proto already carries the flags on `ProtoPackageSummary`. The Kotlin deserializer drops them today; this plan threads them through `GoIRPackage` / `GoIRPackageImpl`, then changes the resolver and entry-point selection to depend on `pkg.isProject` (a derived `!isStdlib && !isDependency`). `selectEntryPoints` is rewritten to walk `cp.packages.values.filter { it.isProject }.flatMap { it.functions }` instead of `cp.allFunctions().filter`.

**Tech Stack:** Kotlin (JVM 11), gradle wrapper at `core/gradlew`, kaml / protobuf-based deserialization, JUnit Jupiter for unit tests.

Working directory: `/drive-testcomp/opentaint-go-rules/opentaint`. Gradle commands run from `/drive-testcomp/opentaint-go-rules/opentaint/core`. Benchmarks at `/drive-testcomp/opentaint-go-rules/benchmarks/{go-owasp-converted-mutated, go-sec-code-mutated}` and the runner script `benchmarks/scan.sh` from the rule-development plan are available (created in commit `c3021704` or later — verify with `ls benchmarks/scan.sh`; if missing, this plan still works using the raw `java -jar` invocation shown in Task 7).

Branch: `saloed/go-dev-tmp` (continue committing directly).

---

## File Structure

| File | Responsibility |
|------|----------------|
| `core/opentaint-ir/go/go-ir-api/src/main/kotlin/org/opentaint/ir/go/api/GoIRPackage.kt` (modify) | Interface gains `isStdlib`, `isDependency`, and derived `isProject`. |
| `core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/impl/GoIRPackageImpl.kt` (modify) | Constructor accepts the two booleans with default `false`. |
| `core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/client/GoIRDeserializer.kt` (modify) | `deserializePackageSummary` passes proto flags; external-stubs package marked `isDependency = true`. |
| `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolver.kt` (modify) | Drop ctor argument; resolve via `pkg.isProject`. |
| `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt` (modify) | Drop `cp.packages.keys.toSet()` arg; rewrite `selectEntryPoints`. |
| `core/src/test/kotlin/org/opentaint/go/sast/sarif/GoSarifGeneratorTest.kt` (modify) | Drop the `setOf("test")` arg from the test resolver instantiation. |
| `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolverTest.kt` (new) | Unit test of the resolver against fake packages. |

---

## Task 1: Extend `GoIRPackage` interface

**Files:**
- Modify: `core/opentaint-ir/go/go-ir-api/src/main/kotlin/org/opentaint/ir/go/api/GoIRPackage.kt`

- [ ] **Step 1: Update the interface**

Replace the file contents with:

```kotlin
package org.opentaint.ir.go.api

/**
 * A Go package with its members.
 *
 * `isStdlib` and `isDependency` come from the SSA server's package summary.
 * `isProject` is the derived "neither" classification — packages declared by
 * the project being analyzed.
 */
interface GoIRPackage {
    val importPath: String
    val name: String
    val isStdlib: Boolean
    val isDependency: Boolean
    val isProject: Boolean get() = !isStdlib && !isDependency
    val functions: List<GoIRFunction>
    val namedTypes: List<GoIRNamedType>
    val globals: List<GoIRGlobal>
    val constants: List<GoIRConst>
    val imports: List<GoIRPackage>
    val initFunction: GoIRFunction?

    fun findFunction(name: String): GoIRFunction?
    fun findNamedType(name: String): GoIRNamedType?
    fun findGlobal(name: String): GoIRGlobal?
    fun findConstant(name: String): GoIRConst?
    fun allMethods(): List<GoIRFunction>
}

/**
 * Set of packages that constitute the analysis scope.
 */
interface GoIRPackageSet {
    val program: GoIRProgram
    val packages: List<GoIRPackage>

    fun findPackage(importPath: String): GoIRPackage?
    fun findNamedType(fullName: String): GoIRNamedType?
    fun findFunction(fullName: String): GoIRFunction?
}
```

- [ ] **Step 2: Compile main**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-ir:go:go-ir-api:compileKotlin
```

Expected: BUILD SUCCESSFUL.

Note: client/test/etc. won't compile yet because `GoIRPackageImpl` doesn't implement the new abstract members. That's expected; Task 2 fixes it.

- [ ] **Step 3: (Defer commit until Task 2 builds clean.)**

---

## Task 2: Add fields to `GoIRPackageImpl`

**Files:**
- Modify: `core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/impl/GoIRPackageImpl.kt`

- [ ] **Step 1: Add the two constructor parameters with default `false`**

Read the file first; then change ONLY the constructor head. After the existing `name: String` line and before `private val loader`, insert:

```kotlin
    override val isStdlib: Boolean = false,
    override val isDependency: Boolean = false,
```

After editing, the class head should look like:

```kotlin
class GoIRPackageImpl(
    override val importPath: String,
    override val name: String,
    override val isStdlib: Boolean = false,
    override val isDependency: Boolean = false,
    private val loader: (() -> Unit)? = null,
) : GoIRPackage {
```

Leave the rest of the class body unchanged (existing equals/hashCode by `importPath` is correct).

- [ ] **Step 2: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-ir:go:go-ir-client:compileKotlin :opentaint-ir:go:go-ir-client:compileTestKotlin
```

Expected: BUILD SUCCESSFUL. (Tests in `GoIRLazyImplTest.kt` continue to build because both new params have defaults — existing calls work unchanged.)

- [ ] **Step 3: Commit Tasks 1+2 together**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/opentaint-ir/go/go-ir-api/src/main/kotlin/org/opentaint/ir/go/api/GoIRPackage.kt \
       core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/impl/GoIRPackageImpl.kt
git commit -m "Add isStdlib/isDependency/isProject to GoIRPackage"
```

---

## Task 3: Wire proto flags through `GoIRDeserializer`

**Files:**
- Modify: `core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/client/GoIRDeserializer.kt`

Two edits inside this file: thread `summary.isStdlib` / `summary.isDependency` into the package created from `ProtoPackageSummary`, and mark the synthetic "external stubs" package as a dependency so unit resolution treats it as external.

- [ ] **Step 1: Update `deserializePackageSummary` (around line 198)**

Replace:

```kotlin
    private fun deserializePackageSummary(summary: ProtoPackageSummary, session: GoIRLazySession) {
        packagesById.getOrPut(summary.id) {
            GoIRPackageImpl(
                importPath = summary.importPath,
                name = summary.name,
                loader = { session.loadPackage(summary.id) },
            )
        }
    }
```

with:

```kotlin
    private fun deserializePackageSummary(summary: ProtoPackageSummary, session: GoIRLazySession) {
        packagesById.getOrPut(summary.id) {
            GoIRPackageImpl(
                importPath = summary.importPath,
                name = summary.name,
                isStdlib = summary.isStdlib,
                isDependency = summary.isDependency,
                loader = { session.loadPackage(summary.id) },
            )
        }
    }
```

- [ ] **Step 2: Mark the external-stubs package as a dependency (around line 133)**

Replace:

```kotlin
        GoIRPackageImpl(importPath = "_external_stubs_", name = "_stubs_")
```

with:

```kotlin
        GoIRPackageImpl(importPath = "_external_stubs_", name = "_stubs_", isDependency = true)
```

- [ ] **Step 3: Compile**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :opentaint-ir:go:go-ir-client:compileKotlin
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 4: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/client/GoIRDeserializer.kt
git commit -m "Thread is_stdlib/is_dependency through Go IR deserializer"
```

---

## Task 4: Simplify `GoUnitResolver`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolver.kt`

- [ ] **Step 1: Replace the file contents**

```kotlin
package org.opentaint.go.sast.dataflow

import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.go.api.GoIRFunction

class GoUnitResolver : UnitResolver<GoIRFunction> {
    data class GoPackageUnit(val pkgImportPath: String) : UnitType

    override fun resolve(method: GoIRFunction): UnitType {
        val pkg = method.pkg ?: return UnknownUnit
        return if (pkg.isProject) GoPackageUnit(pkg.importPath) else UnknownUnit
    }
}
```

- [ ] **Step 2: Compile main**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: this will FAIL until Task 5 / Task 6 are applied — `GoProjectAnalyzer` and the existing `GoSarifGeneratorTest` still pass the now-removed argument. The error will say something like "Too many arguments for public constructor GoUnitResolver". That's expected — proceed to Task 5.

- [ ] **Step 3: (Defer commit until Task 6 builds clean.)**

---

## Task 5: Update `GoProjectAnalyzer`

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt`

Two edits: drop the resolver argument, and rewrite `selectEntryPoints` to iterate project packages.

- [ ] **Step 1: Drop the resolver argument**

Replace:

```kotlin
                unitResolver = GoUnitResolver(cp.packages.keys.toSet()),
```

with:

```kotlin
                unitResolver = GoUnitResolver(),
```

- [ ] **Step 2: Rewrite `selectEntryPoints`**

Replace the existing method:

```kotlin
    private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
        cp.allFunctions().filter { it.hasBody && it.pkg != null && !it.isSynthetic && it.parent == null }
```

with:

```kotlin
    private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
        cp.packages.values
            .filter { it.isProject }
            .flatMap { it.functions }
            .filter { it.hasBody && !it.isSynthetic && it.parent == null }
```

- [ ] **Step 3: Compile main (still expect test failure from `GoSarifGeneratorTest`)**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin
```

Expected: BUILD SUCCESSFUL on main. `:compileTestKotlin` will still fail until Task 6.

- [ ] **Step 4: (Defer commit until Task 6 builds clean.)**

---

## Task 6: Update `GoSarifGeneratorTest` resolver instantiation

**Files:**
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/sarif/GoSarifGeneratorTest.kt`

- [ ] **Step 1: Drop the argument**

Find this line (around line 24):

```kotlin
            unitResolver = GoUnitResolver(setOf("test")),
```

Replace with:

```kotlin
            unitResolver = GoUnitResolver(),
```

- [ ] **Step 2: Compile main + test**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :compileKotlin :compileTestKotlin
```

Expected: BUILD SUCCESSFUL on both.

- [ ] **Step 3: Commit Tasks 4+5+6 together**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolver.kt \
       core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt \
       core/src/test/kotlin/org/opentaint/go/sast/sarif/GoSarifGeneratorTest.kt
git commit -m "Resolve Go units by pkg.isProject; scope entry points to project packages"
```

---

## Task 7: Add unit test for `GoUnitResolver`

**Files:**
- Create: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolverTest.kt`

A small JUnit test that verifies the resolver returns `UnknownUnit` for stdlib + dep packages and `GoPackageUnit` for project packages. Uses anonymous-object fakes (no need for the SSA server).

- [ ] **Step 1: Write the test**

```kotlin
package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRPackage
import kotlin.test.assertEquals

class GoUnitResolverTest {
    @Test
    fun `project package resolves to GoPackageUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(fakePackage("example.com/main", isStdlib = false, isDependency = false))
        assertEquals(GoUnitResolver.GoPackageUnit("example.com/main"), resolver.resolve(fn))
    }

    @Test
    fun `stdlib package resolves to UnknownUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(fakePackage("fmt", isStdlib = true, isDependency = false))
        assertEquals(UnknownUnit, resolver.resolve(fn))
    }

    @Test
    fun `dependency package resolves to UnknownUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(fakePackage("github.com/foo/bar", isStdlib = false, isDependency = true))
        assertEquals(UnknownUnit, resolver.resolve(fn))
    }

    @Test
    fun `null package resolves to UnknownUnit`() {
        val resolver = GoUnitResolver()
        val fn = fakeFunction(pkg = null)
        assertEquals(UnknownUnit, resolver.resolve(fn))
    }

    private fun fakePackage(importPath: String, isStdlib: Boolean, isDependency: Boolean): GoIRPackage =
        object : GoIRPackage {
            override val importPath = importPath
            override val name = importPath.substringAfterLast('/')
            override val isStdlib = isStdlib
            override val isDependency = isDependency
            override val functions = emptyList<GoIRFunction>()
            override val namedTypes = emptyList<org.opentaint.ir.go.api.GoIRNamedType>()
            override val globals = emptyList<org.opentaint.ir.go.api.GoIRGlobal>()
            override val constants = emptyList<org.opentaint.ir.go.api.GoIRConst>()
            override val imports = emptyList<GoIRPackage>()
            override val initFunction: GoIRFunction? = null
            override fun findFunction(name: String) = null
            override fun findNamedType(name: String) = null
            override fun findGlobal(name: String) = null
            override fun findConstant(name: String) = null
            override fun allMethods() = emptyList<GoIRFunction>()
        }

    private fun fakeFunction(pkg: GoIRPackage?): GoIRFunction {
        val resolvedPkg = pkg
        return object : GoIRFunction {
            override val name = "fn"
            override val fullName = "${pkg?.importPath ?: "?"}.fn"
            override val pkg = resolvedPkg
            override val signature get() = error("not used")
            override val params = emptyList<org.opentaint.ir.go.api.GoIRParameter>()
            override val freeVars = emptyList<org.opentaint.ir.go.api.GoIRFreeVar>()
            override val position = null
            override val isMethod = false
            override val receiverType = null
            override val isPointerReceiver = false
            override val isExported = true
            override val isSynthetic = false
            override val syntheticKind: String? = null
            override val body = null
            override val parent = null
            override val anonymousFunctions = emptyList<GoIRFunction>()
            override val typeParams = emptyList<org.opentaint.ir.go.api.GoIRTypeParamDecl>()
        }
    }
}
```

- [ ] **Step 2: Compile + run the test**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :test --tests "org.opentaint.go.sast.dataflow.GoUnitResolverTest"
```

Expected: all 4 tests pass.

- [ ] **Step 3: Commit**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint
git add core/src/test/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolverTest.kt
git commit -m "Add GoUnitResolver unit test for project / stdlib / dep classification"
```

---

## Task 8: Verify on a `samples-go-massive` sample

**Files:** none — build + run only.

- [ ] **Step 1: Rebuild fat jar**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
./gradlew :projectAnalyzerJar
```

Expected: BUILD SUCCESSFUL.

- [ ] **Step 2: Smoke-run on `cmdinj_01_env_basic`**

```bash
mkdir -p /tmp/go-smoke && rm -rf /tmp/go-smoke/results && mkdir -p /tmp/go-smoke/results
SAMPLE_DIR=/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-go-querylang/samples-go-massive/cmdinj_01_env_basic
cat > /tmp/go-smoke/project.yaml <<EOF
projectRoot: $SAMPLE_DIR
goProjects:
  - projectDir: $SAMPLE_DIR
javaProjects: []
EOF
GOIR_SERVER_BINARY=/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-ir/go/go-ssa-server/go-ssa-server \
/home/sobol/.opentaint/install/jre/bin/java -Xmx4g \
  -jar /drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer.jar \
  --project /tmp/go-smoke/project.yaml \
  --output-dir /tmp/go-smoke/results \
  --sarif-file-name report.sarif \
  --track-external-methods 2>&1 | tail -10
ls -la /tmp/go-smoke/results
```

Expected:
- Exit cleanly (no `Fail Go analysis`).
- `report.sarif`, `external-methods-without-rules.yaml`, `external-methods-with-rules.yaml` exist.
- Compared to the wiring-phase smoke, `external-methods-without-rules.yaml` may now show stdlib entries even without rules — because the sample's `util` package is "project" but `os.Getenv` (called inside it from the test fixture) lives in stdlib.

- [ ] **Step 3: (No commit; this is a verification step.)**

---

## Task 9: Verify on both benchmarks

**Files:** none — build + run only. Uses `benchmarks/scan.sh` if available.

- [ ] **Step 1: Confirm scan.sh exists or fall back to manual invocations**

```bash
ls -la /drive-testcomp/opentaint-go-rules/benchmarks/scan.sh 2>/dev/null && echo "have scan.sh" || echo "NO scan.sh — use manual java -jar"
```

- [ ] **Step 2a: (If scan.sh exists) Run both benchmarks**

```bash
/drive-testcomp/opentaint-go-rules/benchmarks/scan.sh both 2>&1 | tee /tmp/scan-after-unitresolver.log
```

- [ ] **Step 2b: (If scan.sh does NOT exist) Run both benchmarks via java -jar**

For each of `go-owasp-converted-mutated`, `go-sec-code-mutated`:

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks/<bench>
rm -rf .opentaint/results && mkdir -p .opentaint/results
GOIR_SERVER_BINARY=/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-ir/go/go-ssa-server/go-ssa-server \
/home/sobol/.opentaint/install/jre/bin/java -Xmx8g \
  -jar /drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer.jar \
  --project .opentaint/project/project.yaml \
  --output-dir .opentaint/results \
  --sarif-file-name baseline.sarif \
  --track-external-methods 2>&1 | tail -10
```

- [ ] **Step 3: Confirm external-methods YAMLs are now populated**

```bash
for bench in go-owasp-converted-mutated go-sec-code-mutated; do
  echo "=== $bench ==="
  wc -l /drive-testcomp/opentaint-go-rules/benchmarks/$bench/.opentaint/results/external-methods-without-rules.yaml \
        /drive-testcomp/opentaint-go-rules/benchmarks/$bench/.opentaint/results/external-methods-with-rules.yaml
  head -20 /drive-testcomp/opentaint-go-rules/benchmarks/$bench/.opentaint/results/external-methods-without-rules.yaml
done
```

Expected: `external-methods-without-rules.yaml` is no longer 3 bytes (`[]\n`). It should contain a non-trivial number of entries — stdlib + dep methods reached during analysis (e.g. `fmt.Sprintf`, `strings.Replace`, `database/sql.*.Query`, …). Exact count depends on what flow happens with the current (still rule-less) analyzer; even a small number proves the wiring works.

Note: with zero Go rules in the builtin set, the analyzer may still produce few external entries (no taint to track). The mere presence of any non-trivial dep methods in the file confirms the fix is working end-to-end. The full value of this change materializes once rules ship — at which point `external-methods-without-rules.yaml` becomes the canonical iteration signal for adding propagators.

- [ ] **Step 4: (No commit — verification only.)**

---

## End

After Task 9, the SSA server's `is_stdlib` / `is_dependency` flags drive the analyzer's project boundary. `selectEntryPoints` iterates only project packages. `external-methods-without-rules.yaml` becomes a useful diagnostic once rules ship taint into the analysis.

Resume the rule-development plan at `docs/superpowers/plans/2026-05-26-go-rule-development.md` after this lands.

---

## Self-review notes

- **Spec coverage:** every section in the spec maps to a task. Interface change → Task 1. Impl plumbing → Task 2. Deserializer wiring → Task 3. Resolver simplification → Task 4. Analyzer call site + entry-point rewrite → Task 5. Test call site → Task 6. Unit test for the resolver → Task 7. Smoke verification → Tasks 8-9.
- **No placeholders:** all code blocks are runnable; all grep targets are concrete file paths and line numbers (`GoIRDeserializer.kt:198` / `:133` etc.).
- **Type consistency:** `isStdlib`, `isDependency`, `isProject` consistently named across interface, impl, deserializer, resolver, and tests. `GoUnitResolver` has no constructor parameter after Task 4, consistently reflected in Task 5 (`GoUnitResolver()`) and Task 6 (`GoUnitResolver()`). Test fake uses anonymous-object syntax compatible with the new interface (covers all interface members so it actually compiles).

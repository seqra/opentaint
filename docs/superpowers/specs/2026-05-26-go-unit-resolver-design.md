# Go UnitResolver + Entry-Point Selection — Project vs Dependency Design

## Goal

Scope the Go analyzer to project code only:

1. `GoUnitResolver` returns `UnknownUnit` for stdlib and third-party
   dependency packages so the IFDS engine only walks project-internal
   code. External methods then surface through the existing
   `external-methods-without-rules.yaml` mechanism and become candidates
   for rule/approximation modeling.
2. `GoProjectAnalyzer.selectEntryPoints` picks only project-package
   functions as entry points — without this filter the analyzer would
   start fresh runs from every stdlib function with a body, wasting time
   even though the unit resolver would short-circuit them.

## Problem

Today `GoUnitResolver` is constructed with `projectImportPaths =
cp.packages.keys.toSet()` — every package the SSA loaded (which includes
stdlib and all transitive deps). Result:

- Every function is treated as a project function.
- The analyzer walks bodies of stdlib functions (`fmt.Sprintf` internals,
  `os.Open`, …), wasting time and inviting precision issues.
- `external-methods-without-rules.yaml` is empty — nothing is "external".

## Existing facts (no new info to discover)

The SSA server already classifies packages per request via
`ProtoPackageSummary` (`core/opentaint-ir/go/proto/goir/service.proto:50`):

```
bool is_stdlib = 8;
bool is_dependency = 9;
string module_path = 6;
string module_dir = 7;
```

Populated at `core/opentaint-ir/go/go-ssa-server/lazy_sessions.go:341-342`:

```go
pp.IsStdlib     = pkg.Module == nil && !strings.Contains(pkg.PkgPath, ".")
pp.IsDependency = !rootPaths[pkg.PkgPath]
```

The Kotlin deserializer currently discards both flags — it only carries
`importPath` and `name` into `GoIRPackageImpl`.

## Design

### 1. Extend `GoIRPackage`

```kotlin
interface GoIRPackage {
    val importPath: String
    val name: String
    val isStdlib: Boolean
    val isDependency: Boolean
    val isProject: Boolean get() = !isStdlib && !isDependency
    // ... existing members unchanged
}
```

`isProject` is a derived convenience — the underlying booleans stay primary
so consumers can distinguish stdlib vs dep when useful.

### 2. Plumb flags through `GoIRPackageImpl`

```kotlin
class GoIRPackageImpl(
    override val importPath: String,
    override val name: String,
    override val isStdlib: Boolean,
    override val isDependency: Boolean,
    private val loader: (() -> Unit)? = null,
) : GoIRPackage { ... }
```

`GoIRDeserializer.deserializePackageSummary` reads `summary.isStdlib` and
`summary.isDependency` from the proto and passes them in.

### 3. Simplify `GoUnitResolver`

```kotlin
class GoUnitResolver : UnitResolver<GoIRFunction> {
    data class GoPackageUnit(val pkgImportPath: String) : UnitType

    override fun resolve(method: GoIRFunction): UnitType {
        val pkg = method.pkg ?: return UnknownUnit
        return if (pkg.isProject) GoPackageUnit(pkg.importPath) else UnknownUnit
    }
}
```

The constructor argument disappears. The new behavior is uniform across
benchmarks regardless of how many packages the SSA loaded.

### 4. Update `GoProjectAnalyzer` call site and entry-point selection

Drop the `cp.packages.keys.toSet()` argument:

```kotlin
unitResolver = GoUnitResolver(),
```

Tighten the entry-point filter to project packages only. Iterate by
package, not by `allFunctions()` — `allFunctions()` walks every loaded
package including stdlib and deps; building a list of those and then
filtering is wasteful. Start from `cp.packages` and only inspect project
packages.

```kotlin
private fun selectEntryPoints(cp: GoIRProgram): List<GoIRFunction> =
    cp.packages.values
        .filter { it.isProject }
        .flatMap { it.functions }
        .filter { it.hasBody && !it.isSynthetic && it.parent == null }
```

The instruction filters (`hasBody`, `!isSynthetic`, `parent == null`)
stay as-is — they exclude declaration-only functions, compiler-synthetic
wrappers, and nested anonymous closures.

### 5. Test fixtures

`samples-go-massive/` tests build their own resolver inline (`UtilUnitResolver`
in `GoMassiveSampleTest.kt` / `GoSampleBasedTest.kt`) — they don't use
`GoUnitResolver`. They keep working unchanged.

If a future test wants the new behavior but with a different project
definition (e.g., a sample where the "project" is the test fixture
directory rather than what the SSA server classifies), it can supply its
own `UnitResolver<GoIRFunction>` — both `GoTaintAnalyzer` and the inline
test harnesses accept any `UnitResolver<GoIRFunction>`, so subclassing or
substituting is trivial.

## Verification

End-to-end test on both benchmarks:

```bash
benchmarks/scan.sh both
```

For each benchmark, check the post-fix `external-methods-without-rules.yaml`:

- **Before fix**: empty (`[]`) because every package counts as project.
- **After fix**: non-empty, populated with stdlib + dep methods reached on
  tainted paths during analysis. Concretely: methods like `fmt.Sprintf`,
  `strings.Replace`, etc. that the analyzer needed to traverse but had no
  body for (now considered external).

The exact size will depend on how much flow the (still-absent) Go rules
push — until rules exist, both lists may still be small; the key check is
that the list **can** populate now.

## Out of scope

- Refining stdlib classification (the SSA server's heuristic
  `pkg.Module == nil && !strings.Contains(pkg.PkgPath, ".")` is good
  enough and out of scope for this change).
- Module-path-aware sub-classification (e.g., distinguishing
  `golang.org/x/...` ancillary deps from external 3rd-party). Not needed
  for the analyzer's correctness.
- Test-side `UtilUnitResolver` consolidation — only refactor if the
  default resolver proves insufficient for the sample tests.

## File-level change list

- `core/opentaint-ir/go/go-ir-api/src/main/kotlin/org/opentaint/ir/go/api/GoIRPackage.kt` — interface gains `isStdlib`, `isDependency`, derived `isProject`.
- `core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/impl/GoIRPackageImpl.kt` — constructor adds two booleans.
- `core/opentaint-ir/go/go-ir-client/src/main/kotlin/org/opentaint/ir/go/client/GoIRDeserializer.kt` — `deserializePackageSummary` passes the flags.
- `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoUnitResolver.kt` — drop ctor arg; resolve via `pkg.isProject`.
- `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt` — `unitResolver = GoUnitResolver()`; `selectEntryPoints` filters via `pkg?.isProject == true`.

## Risks / open questions

- Will `samples-go-massive` continue to function unchanged? They use
  `UtilUnitResolver`, not `GoUnitResolver`. No impact expected. Smoke-test
  one sample after the change.
- Other call sites of `GoUnitResolver(...)`? `grep -rn` may surface tests
  that pass a set of import paths; if found, drop the argument.

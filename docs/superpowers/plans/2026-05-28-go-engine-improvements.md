# Go Engine Improvements Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Close the four confirmed false-negative taint patterns (strings.Builder, container/list, comma-ok type-assert, deep nested struct fields) in the Go analyzer, then confirm benchmark recall improves.

**Architecture:** Each pattern already has a `@Disabled` regression test (`001T` should reach a sink, `002F` should not) and a per-instruction fact trace in its sample `.go` file. Patterns 1–2 are config/loader fixes; Patterns 5–6 are surgical fixes to existing arms of `GoMethodSequentFlowFunction`. The TDD red state is the existing `@Disabled` test: remove `@Disabled`, watch it fail, fix, watch it pass.

**Tech Stack:** Kotlin, Gradle, the OpenTaint IFDS taint engine (`opentaint-go-dataflow`), bundled YAML passthrough config (`opentaint-config/go-config`).

---

## Preliminaries — environment

Every test/build command in this plan runs from the `core/` module directory with `protoc` on PATH and the broken Python venv task excluded:

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
export PATH="/home/sobol/local/bin:$PATH"     # protoc 25.1 lives here
```

Single-test invocation template:

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.<Class>.<method>' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```

The diagnostic helper `AnalysisTest.printFactsAt(entryPoint)` dumps every instruction's fact set to stdout and to `/tmp/go-engine-roadmap-facts/<entry>.txt`. `EngineRoadmapDiagnosticTest` calls it for each pattern's `001T`.

Source of truth for expected behaviour: `docs/superpowers/specs/2026-05-28-go-engine-improvements-roadmap-design.md`.

---

## Task 1: Pattern 1 — `strings.Builder` passthrough rules

**Files:**
- Create: `core/opentaint-config/go-config/config/go-config/strings.builder.yaml`
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/Pattern01StringsBuilderTest.kt` (remove `@Disabled`)
- Reference test: `core/samples/src/main/go/stdlib_strings_builder.go` (already in repo)

- [ ] **Step 1: Confirm the test currently fails (red)**

Remove the `@Disabled` line from `stringsBuilderWrite001T` in `Pattern01StringsBuilderTest.kt`:

```kotlin
    @Test fun stringsBuilderWrite001T() = assertReachable("test.stringsBuilderWrite001T")
    @Test fun stringsBuilderWrite002F() = assertNotReachable("test.stringsBuilderWrite002F")
```

Run:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.Pattern01StringsBuilderTest' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: `stringsBuilderWrite001T` FAILS ("Sink was not reached"); `002F` PASSES.

- [ ] **Step 2: Add the bundled config**

Create `core/opentaint-config/go-config/config/go-config/strings.builder.yaml`:

```yaml
passThrough:
- function:
    package: strings
    type: Builder
    name: WriteString
    receiver: true
  copy:
  - from: arg(0)
    to: this
- function:
    package: strings
    type: Builder
    name: Write
    receiver: true
  copy:
  - from: arg(0)
    to: this
- function:
    package: strings
    type: Builder
    name: WriteByte
    receiver: true
  copy:
  - from: arg(0)
    to: this
- function:
    package: strings
    type: Builder
    name: WriteRune
    receiver: true
  copy:
  - from: arg(0)
    to: this
- function:
    package: strings
    type: Builder
    name: String
    receiver: true
  copy:
  - from: this
    to: result
```

- [ ] **Step 3: Verify the test passes (green)**

Run the same command as Step 1.
Expected: both `stringsBuilderWrite001T` and `002F` PASS.

- [ ] **Step 4: Confirm the post-fix trace**

Run:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EngineRoadmapDiagnosticTest.diag_p01_stringsBuilderWrite001T' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
cat /tmp/go-engine-roadmap-facts/test_stringsBuilderWrite001T.txt
```
Expected: the `WriteString` line now shows a fact on the Builder receiver, and `util.Sink(out)` shows a non-∅ fact.

- [ ] **Step 5: Update the sample annotation and commit**

Replace the "Empirical engine status: FAIL" block in `core/samples/src/main/go/stdlib_strings_builder.go` with the post-fix trace from Step 4 and mark it PASS (resolved 2026-05-28).

```bash
git add core/opentaint-config/go-config/config/go-config/strings.builder.yaml \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/Pattern01StringsBuilderTest.kt \
  core/samples/src/main/go/stdlib_strings_builder.go
git commit -m "Pattern 1: add strings.Builder passthrough rules"
```

---

## Task 2: Pattern 2 — `container/list` via Go pseudo-accessor loader mapping

**Files:**
- Modify: `core/opentaint-config/go-config/src/main/kotlin/org/opentaint/go/config/GoConfigLoader.kt` (`parseGoPositionModifier`)
- Modify: `core/opentaint-go-querylang/src/test/kotlin/org/opentaint/dataflow/go/rules/GoConfigLoaderTest.kt` (add assertion)
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/Pattern02ContainerListTest.kt` (remove `@Disabled`)
- Reference test: `core/samples/src/main/go/stdlib_container_list.go` (already in repo)

- [ ] **Step 1: Confirm the loader currently drops the rule (red, unit level)**

Add a failing assertion to `GoConfigLoaderTest.kt` after the existing `bundledConfigLoadsAndContainsExpectedEntries` test:

```kotlin
    @Test
    fun containerListPushBackRuleSurvivesLoading() {
        val config = assertNotNull(GoConfigLoader.getConfig())
        val pushBack = config.passThrough.firstOrNull {
            (it.function as? GoNameMatcher.Simple)?.name?.endsWith("container/list.List).PushBack") == true
                || (it.function as? GoNameMatcher.Simple)?.name == "container/list.List.PushBack"
        }
        assertNotNull(pushBack, "container/list PushBack rule dropped during loading")
        assertTrue(pushBack.copy.isNotEmpty(), "PushBack copy actions were dropped")
    }
```

Run:
```bash
./gradlew :opentaint-go-querylang:test \
  --tests 'org.opentaint.dataflow.go.rules.GoConfigLoaderTest.containerListPushBackRuleSurvivesLoading' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: FAILS — the rule is dropped (the receiver-method matcher emits names `(container/list.List).PushBack` / `(*container/list.List).PushBack`; adjust the `endsWith` in the assertion to whichever the loader actually emits — confirm by printing the loaded names first if needed).

- [ ] **Step 2: Capture the read-side accessor for `e.Value`**

Run the diagnostic to see what FieldAccessor the real `e.Value` read produces (needed to match the rule's `Value` field type):

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EngineRoadmapDiagnosticTest.diag_p02_containerListPushFront001T' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
cat /tmp/go-engine-roadmap-facts/test_containerListPushFront001T.txt
```
Note the `&e.Value` line — the read produces `FieldAccessor("container/list.Element", "Value", <fieldType>)`. Record `<fieldType>` (expected `interface{}` or `any`).

- [ ] **Step 3: Map the Go pseudo-accessors in the loader**

In `GoConfigLoader.kt`, replace `parseGoPositionModifier` with a version that recognises the Go pseudo-accessor forms before the generic `PositionModifier.deserialize` fallback:

```kotlin
private val goFieldModifier = Regex("""\.([^#]+)#([^#]+)""")  // two-part .Type#field

private fun parseGoPositionModifier(str: String): PositionModifier? {
    // Container/collection element pseudo-accessors → ArrayElement (ElementAccessor).
    when (str) {
        ".[*]", "[*]" -> return PositionModifier.ArrayElement
        ".<map>#<value>", ".<map>#<key>" -> return PositionModifier.ArrayElement
        ".<pointer>#<deref>" -> return null // deref carries the whole-value fact; no accessor
    }
    // Two-part `.Type#field`. `<element>` on any container type → ArrayElement.
    val twoPart = goFieldModifier.matchEntire(str)
    if (twoPart != null) {
        val (className, field) = twoPart.destructured
        if (field == "<element>") return PositionModifier.ArrayElement
        // Real field: synthesise a Field modifier. fieldType must match what the
        // read site produces; the engine's FieldAccessor includes fieldType, so
        // use the wildcard the read side resolves to (see Step 2).
        return PositionModifier.Field(className, field, GO_FIELD_TYPE_WILDCARD)
    }
    return runCatching { PositionModifier.deserialize(str) }.getOrNull()
}
```

where `GO_FIELD_TYPE_WILDCARD` is the `fieldType` recorded in Step 2 (e.g. `"interface{}"`). Add it as a top-level `private const val`.

NOTE: `.<pointer>#<deref>` returning `null` drops one modifier from a multi-modifier position; the existing `mods.size != strings.size - 1` guard in `toPositionBaseWithModifiers` would then reject the whole position. Adjust that guard to tolerate intentionally-dropped deref modifiers — change `mapNotNull` over modifiers so a `null` from `<deref>` is filtered without failing the position. If only `<deref>` was dropped, keep the remaining modifiers; if a genuinely-unparseable modifier appears, still fail. Implement by distinguishing "deliberately empty" (deref) from "parse failure": have `parseGoPositionModifier` return a sentinel for deref and filter it explicitly in the caller.

- [ ] **Step 4: Verify the loader unit test passes (green)**

Run the Step 1 command. Expected: PASS (rule retained with non-empty `copy`).

- [ ] **Step 5: Verify the dataflow test and trace**

Remove `@Disabled` from `containerListPushFront001T` in `Pattern02ContainerListTest.kt`, then:

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.Pattern02ContainerListTest' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: `containerListPushFront001T` and `002F` PASS.

If `001T` still fails, run `diag_p02_containerListPushFront001T` and inspect where the chain breaks. If the break is at the `e.Value` read (the `.Value` fact exists on `e` but the read yields nothing), the residual is the store-back/field-read mechanism — defer to Task 4 (Pattern 6) and keep `001T` `@Disabled` with a note pointing at Task 4. Otherwise iterate on the fieldType wildcard until the read accessor matches.

- [ ] **Step 6: Commit**

```bash
git add core/opentaint-config/go-config/src/main/kotlin/org/opentaint/go/config/GoConfigLoader.kt \
  core/opentaint-go-querylang/src/test/kotlin/org/opentaint/dataflow/go/rules/GoConfigLoaderTest.kt \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/Pattern02ContainerListTest.kt \
  core/samples/src/main/go/stdlib_container_list.go
git commit -m "Pattern 2: map Go pseudo-accessors in GoConfigLoader"
```

---

## Task 3: Pattern 5 — comma-ok type-assert taints the value tuple slot

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/analysis/GoMethodSequentFlowFunction.kt` (`handleAssign`)
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/TypeOpsTest.kt` (remove `@Disabled` on `typeSwitchBinding001T`, and on the pre-existing `typeAssertOk001T`)
- Reference: `core/samples/src/main/go/type_ops.go`

**Root cause (from spec):** `exprToAccess` maps `GoIRTypeAssertExpr` to `singleOperandAccess(expr.x)` for both plain and comma-ok forms — copying the operand fact to the WHOLE result register. But a comma-ok assert returns a tuple `(value, ok)`, and the downstream `extract #0` reads the fact at `result.tuple$0` (via `tupleFieldAccessor`). Whole-result fact has no tuple accessor → extract drops it. Fix: for `commaOk == true`, taint the value slot `result.tuple$0`, leaving the `ok` slot clean.

- [ ] **Step 1: Confirm the test fails (red)**

Remove `@Disabled` from `typeSwitchBinding001T` in `TypeOpsTest.kt`. Run:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.TypeOpsTest.typeSwitchBinding001T' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: FAILS ("Sink was not reached").

- [ ] **Step 2: Add the comma-ok special case in `handleAssign`**

In `GoMethodSequentFlowFunction.kt`, add an import for the expr type:

```kotlin
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
```

In `handleAssign`, before the `exprToAccess` call (after the string-concat special case at the existing `if (expr is GoIRBinOpExpr ...)` block), add:

```kotlin
        if (expr is GoIRTypeAssertExpr && expr.commaOk) {
            return handleCommaOkTypeAssert(initialFact, currentFact, registerBase, expr)
        }
```

Add the handler method (model the gen logic on `handleSimpleAssign` + the multi-return tuple prepend in `handleReturn`):

```kotlin
    private fun handleCommaOkTypeAssert(
        initialFact: InitialFactAp?,
        currentFact: FinalFactAp,
        registerBase: AccessPathBase,
        expr: GoIRTypeAssertExpr,
    ): Set<Sequent> {
        val result = mutableSetOf<Sequent>()

        // Kill: the register is overwritten by the assert result.
        if (currentFact.base != registerBase) {
            result.add(Sequent.Unchanged)
        }

        // Gen: if the operand carries a fact, taint the value slot (tuple index 0)
        // of the (value, ok) result. The `ok` bool slot stays clean.
        val operandBase = GoFlowFunctionUtils.accessPathBase(expr.x, method)
        if (operandBase != null && currentFact.base == operandBase) {
            val valueSlot = GoFlowFunctionUtils.tupleFieldAccessor(0, expr.type)
            val newFact = currentFact.rebase(registerBase).prependAccessor(valueSlot)
            result.add(makeEdge(initialFact, newFact))
        }

        return result
    }
```

- [ ] **Step 3: Verify Pattern 5 passes (green)**

Run the Step 1 command. Expected: `typeSwitchBinding001T` PASSES.

- [ ] **Step 4: Verify the two pre-existing comma-ok tests also unblock**

The same root cause gates the already-`@Disabled` `typeAssertOk001T` (in `TypeOpsTest`) and `mapCommaOk001T` (in `MapOpsTest`). Remove `@Disabled` from `typeAssertOk001T`/`typeAssertOk002F` and run:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.TypeOpsTest' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: `typeAssertOk001T` PASSES, `typeAssertOk002F` PASSES, all other TypeOps tests still PASS. If `mapCommaOk001T` (MapOpsTest) also passes now, un-disable it too; if not, leave it disabled with a note — its tuple comes from a map-lookup `GoIRLookupExpr,ok` shape that may need the same treatment in a different arm (out of scope here).

- [ ] **Step 5: Confirm the trace and commit**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EngineRoadmapDiagnosticTest.diag_p05_typeSwitchBinding001T' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
cat /tmp/go-engine-roadmap-facts/test_typeSwitchBinding001T.txt
```
Expected: `extract #0` shows a fact on the binding register, the phi shows a fact on `dir`, and `util.Sink(dir)` is non-∅.

Update the Pattern 5 annotation block in `core/samples/src/main/go/type_ops.go` to the post-fix trace (mark PASS, resolved 2026-05-28).

```bash
git add core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/analysis/GoMethodSequentFlowFunction.kt \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/TypeOpsTest.kt \
  core/samples/src/main/go/type_ops.go
git commit -m "Pattern 5: comma-ok type-assert taints the value tuple slot"
```

---

## Task 4: Pattern 6 — store through `&%X.field` chain propagates to the root object

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/GoFlowFunctionUtils.kt` (new `resolveAddrChain`)
- Modify: `core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/analysis/GoMethodSequentFlowFunction.kt` (`handleStore`)
- Modify: `core/src/test/kotlin/org/opentaint/go/sast/dataflow/StructOpsTest.kt` (remove `@Disabled` on `nestedNamedDeep001T`, and on the pre-existing `nestedStructMod001T`)
- Reference: `core/samples/src/main/go/struct_ops.go`

**Root cause (from spec):** `accessForAddr` resolves `&%4.v` only ONE level — `base = accessPathBase(expr.x=%4)`, accessor `.v`. For a nested construction `o := DeepL4{...{v: data}}`, the store `*%5 = data` lands on `var(4).v` (the intermediate temporary) instead of walking `%4=&%3.n1 → %3=&%2.n1 → %2=&%1.n1` back to root `o` as `o.n1.n1.n1.v`. The read side already peels one accessor per `&%X.field` instruction and works once the root carries the fact — so the fix is store-side only.

- [ ] **Step 1: Confirm the test fails (red)**

Remove `@Disabled` from `nestedNamedDeep001T` in `StructOpsTest.kt`. Run:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.StructOpsTest.nestedNamedDeep001T' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: FAILS ("Sink was not reached").

- [ ] **Step 2: Add `resolveAddrChain` to `GoFlowFunctionUtils`**

In `GoFlowFunctionUtils.kt`, add a function that walks a store-address register back through nested `&%X.field` / `&%X[i]` producers to the root base, accumulating accessors leaf-first:

```kotlin
    /**
     * Walks a store-destination address back through nested address-of-field /
     * address-of-element producers to its root base, returning the root and the
     * accessor chain in LEAF-FIRST order (deepest field first).
     *
     * `*%5 = data` where %5 = &%4.v, %4 = &%3.n1, %3 = &%2.n1, %2 = &%1.n1
     * resolves to (LocalVar(1), [.v, .n1, .n1, .n1]).
     *
     * Returns null if the address is not a register-rooted field/element chain
     * (callers fall back to single-level accessForAddr / Simple handling).
     */
    fun resolveAddrChain(addr: GoIRValue, method: GoIRFunction): Pair<AccessPathBase, List<Accessor>>? {
        if (addr !is GoIRRegister) return null
        val accessors = mutableListOf<Accessor>()
        var cur: GoIRValue = addr
        // Bounded by the def-use chain length, which is finite per SSA function.
        while (cur is GoIRRegister) {
            val expr = (findDefInst(cur, method) as? GoIRAssignInst)?.expr
            when (expr) {
                is GoIRFieldAddrExpr -> {
                    accessors.add(fieldAccessorFromAddr(expr))
                    cur = expr.x
                }
                is GoIRIndexAddrExpr -> {
                    accessors.add(ElementAccessor)
                    cur = expr.x
                }
                else -> {
                    // cur is the root local (or a non-address producer).
                    return AccessPathBase.LocalVar(cur.index) to accessors
                }
            }
        }
        val base = accessPathBase(cur, method) ?: return null
        return base to accessors
    }
```

- [ ] **Step 3: Use the chain in `handleStore`**

In `GoMethodSequentFlowFunction.kt` `handleStore`, replace the single-accessor gen in the `Access.RefAccess` branch. Currently:

```kotlin
                // Gen: if value is tainted, write taint into dest.accessor
                if (currentFact.base == valueBase) {
                    val newFact = currentFact.rebase(destBase).prependAccessor(accessor)
                    result.add(makeEdge(initialFact, newFact))
                }
```

Change the gen to resolve the full chain (keep the existing kill/preserve logic above it unchanged — the kill logic correctly uses the immediate `destBase`/`accessor` for the single-level overwrite semantics):

```kotlin
                // Gen: if value is tainted, write taint into the FULL field path
                // resolved back to the root object (not just the immediate temporary).
                if (currentFact.base == valueBase) {
                    val chain = GoFlowFunctionUtils.resolveAddrChain(inst.addr, method)
                    val newFact = if (chain != null) {
                        val (rootBase, accessors) = chain
                        // accessors are leaf-first; prependAccessor builds front-to-back,
                        // so folding leaf-first yields root + [.n1.n1.n1.v].
                        accessors.fold(currentFact.rebase(rootBase)) { f, acc -> f.prependAccessor(acc) }
                    } else {
                        currentFact.rebase(destBase).prependAccessor(accessor)
                    }
                    result.add(makeEdge(initialFact, newFact))
                }
```

Add the import if not present:
```kotlin
import org.opentaint.dataflow.ap.ifds.Accessor
```

- [ ] **Step 4: Verify Pattern 6 passes (green)**

Run the Step 1 command. Expected: `nestedNamedDeep001T` PASSES. Also run `nestedNamedDeep002F` (should PASS — sibling field clean).

- [ ] **Step 5: Verify the pre-existing 2-level test also unblocks**

Remove `@Disabled` from `nestedStructMod001T` in `StructOpsTest.kt` and run the full class:
```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.StructOpsTest' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
```
Expected: `nestedNamedDeep001T`, `nestedStructMod001T` PASS; `nestedStructMod002F`, `nestedStructMod003F` still PASS (no over-taint); all other StructOps tests PASS.

- [ ] **Step 6: Run the full Go dataflow suite to check for regressions**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.*' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks 2>&1 | tail -20
```
Expected: no NEW failures versus the pre-change baseline. The store-chain change is additive (it only widens the gen fact); confirm no `002F`/`003F` negative test flipped to a false positive.

- [ ] **Step 7: Confirm trace, update annotation, commit**

```bash
./gradlew :test --tests 'org.opentaint.go.sast.dataflow.EngineRoadmapDiagnosticTest.diag_p06_nestedNamedDeep001T' \
  -x ':opentaint-ir:python:createPirServerVenv' --rerun-tasks
cat /tmp/go-engine-roadmap-facts/test_nestedNamedDeep001T.txt
```
Expected: the store line shows a fact rooted at `o` with the full `.n1.n1.n1.v` path; each read `&%X.field` peels one accessor; `util.Sink` is non-∅.

Update the Pattern 6 annotation in `core/samples/src/main/go/struct_ops.go` to the post-fix trace (mark PASS, resolved 2026-05-28).

```bash
git add core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/GoFlowFunctionUtils.kt \
  core/opentaint-dataflow-core/opentaint-go-dataflow/src/main/kotlin/org/opentaint/dataflow/go/analysis/GoMethodSequentFlowFunction.kt \
  core/src/test/kotlin/org/opentaint/go/sast/dataflow/StructOpsTest.kt \
  core/samples/src/main/go/struct_ops.go
git commit -m "Pattern 6: store through address chain propagates to root object"
```

---

## Task 5: Benchmark checkpoint after Pattern 6

**Files:** none (verification only)

- [ ] **Step 1: Rebuild the analyzer + autobuilder jars**

```bash
cd /drive-testcomp/opentaint-go-rules/opentaint/core
export PATH="/home/sobol/local/bin:$PATH"
./gradlew :projectAnalyzerJar :opentaint-jvm-autobuilder:projectAutoBuilderJar \
  -x ':opentaint-ir:python:createPirServerVenv'
./gradlew :opentaint-ir:go:buildGoServer    # refresh the SSA server binary
```
Expected: BUILD SUCCESSFUL; jars under `core/build/libs/` and `core/opentaint-jvm-autobuilder/build/libs/` updated.

- [ ] **Step 2: Run both benchmarks**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks && bash scan.sh
```
Expected: both scans complete without "unhandled analyzer exception"; `compare.py` prints a per-CWE TP table for each.

- [ ] **Step 3: Record the delta**

Compare against the baseline (commit `f2dcb263`): go-sec-code-mutated **96.7%** (175/181), go-owasp-converted-mutated **20.3%** (30/148). Capture both per-CWE tables. The owasp number is expected to move (strings.Builder / container/list / deep-struct / type-switch mutation families appear in its misses); sec should hold at or above 96.7%.

If a pattern's unit test is green but the benchmark didn't move for its CWE, diff the benchmark mutation against the isolated sample (the mutation may chain an additional unhandled step) before considering that pattern fully done.

- [ ] **Step 4: Commit the result note**

Append a short "post-Pattern-6 benchmark result" note (date, both TP numbers, per-CWE deltas) to the spec's benchmark-checkpoint section, then:
```bash
git add docs/superpowers/specs/2026-05-28-go-engine-improvements-roadmap-design.md
git commit -m "Record post-Pattern-6 benchmark result"
```

---

## Task 6: CLI `--debug-fact-reachability-sarif` port (optional, after benchmark)

**Files:**
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/dataflow/GoTaintAnalyzer.kt` (add `statementsWithFacts()`)
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalyzer.kt` (honour the flag)
- Modify: `core/src/main/kotlin/org/opentaint/go/sast/project/GoProjectAnalysisOptions.kt` (thread the flag — confirm exact path)
- Create: `core/src/main/kotlin/org/opentaint/go/sast/sarif/GoDebugFactReachabilitySarifGenerator.kt`
- Reference (JVM analog): `core/opentaint-jvm-sast-dataflow/.../JIRTaintAnalyzer.kt:262-276`, `core/src/.../sarif/DebugFactReachabilitySarifGenerator.kt:16-74`, `ProjectAnalyzer.kt:146-149` and `:213-223`

- [ ] **Step 1: Add `statementsWithFacts()` to `GoTaintAnalyzer`**

Mirror `JIRTaintAnalyzer.statementsWithFacts()`. Expose the same engine-query the test helper already uses:

```kotlin
    fun statementsWithFacts(): Map<CommonInst, Set<FinalFactAp>> {
        val out = hashMapOf<MethodEntryPoint, Map<CommonInst, Set<FinalFactAp>>>()
        ifdsEngine.allUnits().forEach { unit ->
            val runner = ifdsEngine.findUnitRunner(unit) ?: return@forEach
            runner.collectAllIntraProceduralFacts(out)
        }
        val merged = hashMapOf<CommonInst, MutableSet<FinalFactAp>>()
        for ((_, stmtFacts) in out) {
            for ((stmt, facts) in stmtFacts) merged.getOrPut(stmt) { hashSetOf() }.addAll(facts)
        }
        return merged
    }
```

Confirm the field holding the engine instance in `GoTaintAnalyzer` (the test helper constructs `TaintAnalysisUnitRunnerManager` directly; the analyzer keeps it as a member — find its name and reuse it).

- [ ] **Step 2: Create the SARIF generator**

Model `GoDebugFactReachabilitySarifGenerator` on `DebugFactReachabilitySarifGenerator.kt:16-74`: one SARIF result per `(statement, fact)`, ruleID `s_<index>`, message = fact `toString()`, location = statement file+line from `GoInstLocation.position`.

- [ ] **Step 3: Honour the flag in `GoProjectAnalyzer`**

After `analyzer.analyzeWithIfds(...)`, when the debug flag is set, call `analyzer.statementsWithFacts()` and write `result-dir/debug-fact-reachability.sarif` via the new generator. Mirror `ProjectAnalyzer.kt:146-149` / `:213-223`. Thread the flag from the existing `--debug-fact-reachability-sarif` CLI option (already in `DebugOptions.factReachabilitySarif`) into `GoProjectAnalysisOptions`.

- [ ] **Step 4: Smoke test on a benchmark**

```bash
cd /drive-testcomp/opentaint-go-rules/benchmarks/go-sec-code-mutated
GOIR_SERVER_BINARY=/drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-ir/go/go-ssa-server/go-ssa-server \
opentaint --experimental scan --project-model .opentaint/project \
  --analyzer-jar /drive-testcomp/opentaint-go-rules/opentaint/core/build/libs/opentaint-project-analyzer.jar \
  --autobuilder-jar /drive-testcomp/opentaint-go-rules/opentaint/core/opentaint-jvm-autobuilder/build/libs/opentaint-project-auto-builder.jar \
  --ruleset /drive-testcomp/opentaint-go-rules/benchmarks/rules \
  -o .opentaint/results/report.sarif \
  --debug-fact-reachability-sarif --rule-id go-command-injection
```
Expected: `debug-fact-reachability.sarif` written next to the report with per-statement fact results.

- [ ] **Step 5: Commit**

```bash
git add core/src/main/kotlin/org/opentaint/go/sast/
git commit -m "Port --debug-fact-reachability-sarif to the Go analyzer"
```

---

## Final review

After all tasks, dispatch a code-review over the full diff (`git diff f2dcb263..HEAD`) focused on: no `002F`/negative test flipped to false-positive; the store-chain and comma-ok changes don't over-taint; the loader pseudo-accessor mapping doesn't silently swallow genuinely-malformed config. Then use superpowers:finishing-a-development-branch.

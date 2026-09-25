# Mark-set shallow scan: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Implement the mark-set shallow scan on `main`, as specified in `docs/markset-shallow-scan-spec.md`:

- a statement-level rule selection computed from the prescan's call graph and residual conditions;
- installed in the full scan through a filtering rules provider;
- behind `--mark-set-scan`.

**Architecture:**

- A language-agnostic pure core in `opentaint-dataflow` (`org.opentaint.dataflow.ap.ifds.markset`). It holds the conditions, the program, the scan algorithm, and a recorder that turns engine callbacks into a program.
- JVM glue in `opentaint-jvm-dataflow`: prescan recording hooks and `SelectedTaintRulesProvider`.
- Phase wiring and options in `opentaint-jvm-sast-dataflow`, with the CLI flag in the root project.
- Every algorithmic behaviour is tested against the Lean reference through oracle JSON.

**Tech stack:** Kotlin, JUnit5 via `kotlin.test`, kotlinx.serialization JSON (test only), Gradle (root `core/`), Lean 4.33.1 (`formal/markset-scan`).

**Spec:** `docs/markset-shallow-scan-spec.md`. The Lean model is the source of truth.

## Global constraints

- Gradle runs from `core/` with `--offline -x :opentaint-ir:go:buildGoServer`.
- The 52 Go test failures in root `:test` are environmental baseline, not regressions.
- Existing behaviour must be byte-identical when `markSetScan = false`. Every new engine hook is gated on a non-null recorder.
- Code style: match the surrounding code. Tests use `kotlin.test.Test` with backticked sentence names.
- Commits end with `Co-Authored-By: Claude Opus 5.5 (1M context) <noreply@anthropic.com>`. Scope prefix: `feat(core, analyzer):` for core, `test(core, analyzer):` for tests. The CI rule forbids mixing `docs/` and `core/` in one PR, but one branch is fine.
- The flow-insensitive default, relevance on and 4* off must satisfy every oracle case **exactly**.
- Option 4* may over-approximate the Lean relaxed semantics (spec §6.2); oracle tests check ⊇ for it.

---

## File structure

**`opentaint-dataflow`**, under `src/main/kotlin/org/opentaint/dataflow/ap/ifds/markset/`:

| File | Contents |
|---|---|
| `MarkCond.kt` | The condition tree and its single-pass evaluation (`CondEval`) |
| `MarkSetProgram.kt` | `SiteKind`, `MarkSite`, `MarkSetProgram`, `MarkSetOptions`, `MarkSetResult`, `MarkSetStats` |
| `MarkSetScan.kt` | The flow-insensitive algorithm (spec §6.5), with relaxed and relevance variants |
| `FlowSensitiveScan.kt` | Option 3* (spec §9). Task 8. |
| `Scc.kt` | Iterative Tarjan condensation |
| `MarkSetRecorder.kt` | Thread-safe recorder that seals into a `MarkSetInput` (program + id tables) |

Also in `opentaint-dataflow`:
- `ap/ifds/taint/ActionableRules.kt`: `typealias ActionableRules`, the same as on the staged branch.
- `ap/ifds/TaintAnalysisManager.kt`: new members `markSetRecorder()` and `selectStatementRules(...)`, both with defaults.
- `ap/ifds/TaintAnalysisUnitRunner.kt`: edge hook in `subscribeOnMethodSummaries(ZeroToZero, …)`.
- `ap/ifds/TaintAnalysisUnitRunnerManager.kt`: M7, set the failure status before completing.

**`opentaint-jvm-dataflow`:**

| File | Change |
|---|---|
| `jvm/ap/ifds/taint/SelectedTaintRulesProvider.kt` | new, filter semantics |
| `jvm/ap/ifds/taint/MarkSetRecording.kt` | new; maps JVM rule → kind/gens and records |
| `jvm/ap/ifds/taint/JIRTaintAnalysisContext.kt` | record in `prepare*`/static-field paths |
| `jvm/ap/ifds/analysis/JIRAnalysisManager.kt` | recorder param, provider wrap, activate recorder in Prescan |
| `jvm/ap/ifds/analysis/JIRMethodSequentFlowFunction.kt` | Prescan-only exit rules at `JIRThrowInst` |
| `jvm/ap/ifds/analysis/JIRMethodCallFlowFunction.kt` | Prescan-only cleaner and pass-through queries at zero call edges |

**`opentaint-jvm-sast-dataflow`:**

| File | Change |
|---|---|
| `common/sast/dataflow/TaintAnalyzerOptions.kt` | `MarkSetScanOptions` field |
| `common/sast/dataflow/TaintAnalyzer.kt` | `markSetPhase` between prescan and full scan |
| `common/sast/dataflow/MarkSetPhase.kt` | new: fail-open logic, result → `ActionableRules`, logging |
| `jvm/sast/dataflow/JIRTaintAnalyzer.kt` | create the recorder |

**Root:** `src/main/kotlin/org/opentaint/common/sast/CommonAnalysisOptions.kt` and `jvm/sast/runner/ProjectAnalyzerRunner.kt` (CLI flags).

**Tests:**
- `opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/ap/ifds/markset/*Test.kt`
- `opentaint-dataflow/src/test/resources/markset/oracle.json`, produced by `lake exe markset-oracle`
- `opentaint-jvm-dataflow` provider tests
- root `src/test/.../jvm/sast/dataflow/MarkSet*Test.kt` plus the differential switch in `AnalysisTest`
- `opentaint-java-querylang` `TestAnalysisRunner` differential switch

---

### Task 1: Conditions (`MarkCond`)

**Files:** create `markset/MarkCond.kt` and `markset/MarkCondTest.kt`.

**Interfaces (produces):**
```kotlin
package org.opentaint.dataflow.ap.ifds.markset

sealed interface MarkCond {
    data object True : MarkCond
    data object False : MarkCond
    /** `mark`: dense mark id. `literal`: dense id of the (position·access, mark, kind) literal,
     *  used only to count distinct literals of a cube (joined-ness, spec §4.1). */
    data class Lit(val mark: Int, val literal: Int) : MarkCond
    data class And(val args: List<MarkCond>) : MarkCond
    data class Or(val args: List<MarkCond>) : MarkCond
}

/** One-pass evaluation of a tree against a mark set, without DNF expansion:
 *  sat      - some cube ⊆ marks
 *  hasEmpty - the constant-true cube is satisfied
 *  singles  - literal ids L such that the cube {L} is satisfied
 *  big      - some cube with ≥ 2 distinct literals ⊆ marks */
class CondEval(val sat: Boolean, val hasEmpty: Boolean, val singles: Set<Int>, val big: Boolean) {
    /** A cube with ≤ 1 literal is satisfied (per-root test). */
    val smallSat: Boolean get() = hasEmpty || singles.isNotEmpty()
}

fun MarkCond.eval(marks: java.util.BitSet): CondEval
fun MarkCond.atoms(out: java.util.BitSet = java.util.BitSet()): java.util.BitSet
/** Static: the DNF has a cube with ≥ 2 distinct literals (= eval(all marks).big). */
fun MarkCond.hasJoinedCube(): Boolean
```

**Evaluation rules.** These are exact with respect to the DNF, and they are what the tests check.

| Node | sat | hasEmpty | singles | big |
|---|---|---|---|---|
| `True` | true | true | ∅ | false |
| `False` | false | false | ∅ | false |
| `Lit(m, L)`, m ∈ marks | true | false | {L} | false |
| `Lit(m, L)`, m ∉ marks | false | false | ∅ | false |
| `Or(a, b)` | a.sat ∨ b.sat | a.e ∨ b.e | a.s ∪ b.s | a.big ∨ b.big |
| `And(a, b)` | a.sat ∧ b.sat | a.e ∧ b.e | (a.e ? b.s : ∅) ∪ (b.e ? a.s : ∅) ∪ (a.s ∩ b.s) | (a.big ∧ b.sat) ∨ (b.big ∧ a.sat) ∨ ∃La ∈ a.s, Lb ∈ b.s: La ≠ Lb |

N-ary `And`/`Or` fold left, starting from `True`/`False`.

- [ ] **Step 1: write failing tests.**
  - *DNF oracle test.* A test-local `toDnf(): List<Set<Int>>` (cubes as literal sets). For 2,000 random trees (seeded `Random(42)`, depth ≤ 4, ≤ 4 marks, literal ids from `(mark, pos ∈ 0..1)`) and random mark sets, assert:
    - `sat` equals DNF-sat;
    - `smallSat` equals ∃ cube of size ≤ 1 contained in the set;
    - `big` equals ∃ cube of size ≥ 2 contained in the set;
    - `singles` equals `{L | [L] ⊆ set and cube {L} ∈ DNF}`.
  - *Named witnesses from the Lean `Cond` module:*
    - `naiveAny_unsound`: `Or(True, Lit(1,·))` is sat on ∅.
    - `sat_not_join_distributive`: `And(Lit(1,a), Lit(2,b))` is sat on {1,2} and not on {1} or {2}.
    - `tree_vs_dnf_cost`: for k = 12, `andOrChain(12)` evaluates in linear time. Assert the result, and that the test-local DNF has 4096 cubes.
    - Same literal twice: `And(Lit(1,L), Lit(1,L))` has `big = false` and `singles = {L}`.
- [ ] **Step 2:** run `./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --tests 'org.opentaint.dataflow.ap.ifds.markset.MarkCondTest' --offline -x :opentaint-ir:go:buildGoServer`. Expected: compile failure.
- [ ] **Step 3:** implement `MarkCond.kt` exactly per the table.
- [ ] **Step 4:** the tests pass.
- [ ] **Step 5:** commit `feat(core, analyzer): Add mark-only residual conditions for the mark-set scan`.

### Task 2: Program types, the flow-insensitive scan, and oracle tests

**Files:**
- create `markset/MarkSetProgram.kt`, `markset/Scc.kt`, `markset/MarkSetScan.kt`;
- tests `markset/MarkSetScanOracleTest.kt` and `markset/MarkSetScanTest.kt`;
- resource `src/test/resources/markset/oracle.json`;
- `opentaint-dataflow/build.gradle.kts`: add `testImplementation(KotlinDependency.Libs.kotlinx_serialization_json)`.

**Interfaces:**
```kotlin
enum class SiteKind { SOURCE, SINK, PASS_THROUGH }
class MarkSite(val method: Int, val kind: SiteKind, val cond: MarkCond, val gens: IntArray)
class MarkSetProgram(
    val methodCount: Int, val markCount: Int,
    val roots: IntArray,                 // root method ids
    val callees: Array<IntArray>,        // method -> distinct callee methods
    val sites: List<MarkSite>,
    val cleanerAtoms: java.util.BitSet,  // spec §6.3 (4)
)
data class MarkSetOptions(val relaxed: Boolean = false, val relevance: Boolean = true)
class MarkSetStats(val methods: Int, val edges: Int, val sites: Int, val signatures: Int,
                   val distinctRootSets: Int, val outerRounds: Int, val applicableSites: Int,
                   val applicableSinks: Int, val neededMarks: Int)
class MarkSetResult(
    val applicable: java.util.BitSet,              // indices into program.sites
    val needed: java.util.BitSet,                  // marks; all marks if !relevance
    val rootMarks: Map<Int, java.util.BitSet>,     // S_E per root (for tests)
    val stats: MarkSetStats,
)
object MarkSetScan {
    fun run(p: MarkSetProgram, options: MarkSetOptions = MarkSetOptions(),
            checkCancelled: () -> Unit = {}): MarkSetResult
}
object Scc { /** Components in reverse topological order: callees before callers. */
    fun condense(n: Int, succ: Array<IntArray>, reachableFrom: IntArray): Condensation }
class Condensation(val compOf: IntArray /* -1 = unreachable */, val comps: List<IntArray>, val compSucc: Array<IntArray>)
```

**Algorithm.** This follows spec §6.5, on a method graph where U(n) = U(method n).

1. **Condense** the methods reachable from the roots.
2. **Signatures.** A signature is `(cond, gens, kind == SINK)`, interned via a `HashMap<SigKey, Int>`. Per component, `sig(c) = local(c) ∪ ⋃ sig(succ)` as a `BitSet` over signature ids, built bottom-up and hash-consed with `HashMap<BitSet, BitSet>`.
3. **Forced marks.** Keep `X(method)` as a `BitSet` of marks, initially empty. Per component, `xr(c) = ⋃ X(members) ∪ ⋃ xr(succ)`, built bottom-up and hash-consed.
4. **Per root E,** `S_E = closure(sig(comp E), xr(comp E))`, with results cached by `(sig identity, xr identity)`. The closure starts from `xr` and repeats until no change: for each signature in the set whose `cond.eval(S).smallSat` holds, add its gens.
5. **Unions.** `U(c)` is built top-down in topological order: `U(c) = ⋃ U(pred) ∪ ⋃ {S_E | E root in c}`, hash-consed.
6. **Joined and sinkGen pass.** For each site at method m, let `U = U(comp m)` and `e = cond.eval(U)`.
   - Non-sink: fires if `e.big`. With 4*: `cond.hasJoinedCube() && atoms ∩ U ≠ ∅`.
   - Sink: fires if `e.sat` (any cube, method-level; spec §6.1 sinkGen). With 4*: also `hasJoinedCube && atoms ∩ U ≠ ∅`.
   - A firing site adds its gens into `X(m)`.
   - If any `X` changed, go back to step 3 (outer round).
7. **Applicability.** A site at a reachable method m is applicable iff `cond.eval(U(comp m)).sat`. With 4*: also `hasJoinedCube && atoms ∩ U ≠ ∅`. This is `applicable_iff_union` with node = method.
8. **Needed.** If `!relevance`, needed = all marks. Otherwise a least fixpoint:
   - Seeds: `atoms(cond) ∪ gens` of each applicable sink, `cleanerAtoms`, and `atoms(cond)` of each applicable pass-through.
   - Iteration: an applicable site with `gens ∩ N ≠ ∅` adds `atoms(cond)`.
   - Deduplicate by signature.
9. Call `checkCancelled()` once per outer round and every 4,096 closure steps.

**Oracle fixture.**

Generate it with:
```
cd formal/markset-scan && lake exe markset-oracle 400 1 > ../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/resources/markset/oracle.json
```

Schema:
```
{"programs":[{"seed","nodeCount","roots","calls":[[caller,pc,callee]],"pcs":[[node,pc]],
  "sites":[{"node","pc","kind":"source|sink|passThrough","cond":[[[base,mark,negated]]],"gens":[mark]}],
  "cleanerAtoms":[[node,pc,mark]],
  "expected":{"inS":[[root,mark]],"applicable":[siteIndex],"needed":[mark]}}]}
```

Converting a program to `MarkSetProgram`:
- method = node, `callees` = distinct callees from `calls`;
- `cond` = `Or(cubes.map { And(literals.filter { !negated }.map { Lit(mark, literalId(base, mark)) }) })`, where an empty `Or` is `False` and an empty `And` is `True`;
- `cleanerAtoms` = the union of the atoms' marks;
- `markCount` = max mark + 1.

**`MarkSetScanOracleTest`:**
- *Exact mode (default options).* For every program, `rootMarks[E]` equals the expected `inS` of E, restricted to roots. `applicable` equals the expected set. `needed` equals the expected set.
- *4* mode.* Kotlin `applicable ⊇` expected, and `needed ⊇` expected. The model proves `Applicable ⊆ ApplicableRelax`, and ours over-approximates that.
- *Relevance off.* `needed` = all marks.

**`MarkSetScanTest`**, with named Kotlin twins of the Lean witnesses. Each builds the same program by hand:
- **D1** (`d1_*`): two roots with sources A and B, a shared callee, and a sink `And(Lit(A,a0), Lit(B,b1))`. The sink is applicable, and neither root's `S_E` contains both marks.
- **D4** (`backward_closure_necessary`): source → transformer `Lit(1)⇒gen 2` → sink `Lit(2)`. `needed = {1, 2}`.
- **G1** (`sinkgen_zero_ctx_needed`): an end mark from a sink reached from root 1 makes a sink in root 2 applicable.
- **G3** (`naive_relax_unsound`): the three-root joined source. The E3 sink on C is applicable, both exact and with 4*.
- **Recursion:** a cycle A ↔ B with a source in B and a sink in A.
- **Unreachable method:** its sites are never applicable.
- **Cost family** (`fam_speedup`): 1,000 sites sharing one signature under 50 roots. `stats.signatures == 1`, and it finishes in under 1 s.

Steps:
- [ ] **Step 1:** add the JSON test dependency and generate the fixture. The Lean executable exists: `lake build markset-oracle`.
- [ ] **Step 2:** write the oracle test and `MarkSetScanTest`. Run them and expect compile failures.
- [ ] **Step 3:** implement `MarkSetProgram.kt`, `Scc.kt` (iterative Tarjan, no recursion) and `MarkSetScan.kt`.
- [ ] **Step 4:** all tests pass. On a mismatch, **the Lean result wins**: report the program seed and fix the Kotlin side.
- [ ] **Step 5:** commit `feat(core, analyzer): Add the flow-insensitive mark-set scan`.

### Task 3: Recorder (language-agnostic)

**Files:** create `markset/MarkSetRecorder.kt` and `markset/MarkSetRecorderTest.kt`.

**Interfaces:**
```kotlin
class MarkSetRecorder(val maxSites: Int = 20_000_000, val maxEdges: Int = 20_000_000) {
    @Volatile var active: Boolean = false          // true only during Prescan
    @Volatile var overflow: Boolean = false
    fun recordEdge(caller: CommonMethod, call: CommonInst, callee: CommonMethod)
    fun recordStatement(statement: CommonInst)     // statements where the prescan queried rules
    fun recordSite(statement: CommonInst, rule: CommonTaintConfigurationItem, kind: SiteKind,
                   residual: RuleConditionRewriter.ExprOrConstant, gens: List<String>)
    fun recordCleaner(statement: CommonInst, residual: RuleConditionRewriter.ExprOrConstant)
    fun seal(roots: Collection<CommonMethod>): MarkSetInput
}
class SiteRef(val statement: CommonInst, val rule: CommonTaintConfigurationItem, val genMarks: List<String>)
class MarkSetInput(
    val program: MarkSetProgram,
    val sites: List<SiteRef>,                 // parallel to program.sites
    val markNames: List<String>,              // mark id -> name
    val coveredStatements: Set<CommonInst>,
)
```

**Recording rules:**
- All `record*` methods return immediately unless `active`.
- Methods, marks and literals are interned under a lock or with concurrent maps.
- Mark ids come from `TaintMarkAccessor.mark` strings and from gens (`AssignMark.mark.name`).
- Literal ids are keyed by `(position: PositionAccess, markName, anyAccessor: Boolean)`.
- Residual → `MarkCond`:
  - `isTrue` → `True`;
  - `isFalse` → not recorded;
  - `And`/`Or` map recursively over `args`;
  - `ContainsMarkLiteral` / `ContainsMarkOnAnyAccessorLiteral` → `Lit` when `negated == false`, `True` when negated (E5).
- Sites are deduplicated on `(statement, rule, MarkCond)` (M8). The method of a site is `statement.location.method`.
- `recordCleaner` adds the positive atoms' marks to `cleanerAtoms`.
- `overflow = true` when a cap is exceeded; recording then stops.
- `seal` builds `callees` from the edges (deduplicated), roots = the given roots that are known methods, and methods = the union of edge endpoints, site methods and roots.
- **Check E0 (PcWF):** every site's method is a node. It holds by construction; assert it.

- [ ] **Step 1: failing tests.** They use fake `CommonMethod`/`CommonInst`. If the interfaces are too wide, use mockk if it is available (check `libs`); otherwise write small anonymous objects.
  - An inactive recorder records nothing.
  - Negated literals become `True`.
  - `A@arg0 ∧ A@arg1` gets two literal ids, so the cube is joined.
  - Dedup: recording the same site twice keeps one.
  - Two residuals for the same (statement, rule) are both kept.
  - The cap sets `overflow`.
  - `seal` output `MarkSetProgram` structure: callees, roots, site ↔ `SiteRef` alignment.
- [ ] **Steps 2–4:** red, implement, green.
- [ ] **Step 5:** commit `feat(core, analyzer): Add the mark-set prescan recorder`.

### Task 4: Selection mechanism (`ActionableRules` + filtering provider)

**Files:**
- create `opentaint-dataflow/.../ap/ifds/taint/ActionableRules.kt`;
- modify `TaintAnalysisManager.kt`;
- create `opentaint-jvm-dataflow/.../jvm/ap/ifds/taint/SelectedTaintRulesProvider.kt`;
- modify `JIRAnalysisManager.kt`;
- test `opentaint-jvm-dataflow/src/test/kotlin/.../taint/SelectedTaintRulesProviderTest.kt`.

**Interfaces:**
```kotlin
// ActionableRules.kt (identical to saloed/staged-analysis-clean)
typealias ActionableRules = Map<CommonInst, Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>>

// TaintAnalysisManager (new members with defaults; Go keeps them)
fun markSetRecorder(): MarkSetRecorder? = null
fun selectStatementRules(rules: ActionableRules?, coveredStatements: Set<CommonInst>) {}

// SelectedTaintRulesProvider(delegate: TaintRulesProvider) : TaintRulesProvider
fun select(rules: ActionableRules?, coveredStatements: Set<CommonInst>)
```

**Provider semantics** (spec §10, G5/G6), for the six restricted queries: entry-point sources, method sources, exit sources, method sinks, entry sinks, exit sinks.
1. `val base = delegate.query(same args)`.
2. If `selection == null || allRelevant || statement !in covered`, return `base`.
3. Otherwise:
   ```kotlin
   base.mapNotNull { rule ->
       val acts = selected[statement]?.get(rule) ?: return@mapNotNull null
       when (rule) {
           is TaintConfigurationSource -> rule.copyWithActions(rule.actionsAfter.filter { it in acts })
                                              .takeIf { it.actionsAfter.isNotEmpty() }
           else -> rule   // sinks: kept whole
       }
   }
   ```
   `copyWithActions` is a `when` over the four source data classes, using `copy(actionsAfter = …)`.
4. Pass-through, cleaner, static-field, and `selectRules` always delegate.
5. `select` swaps an immutable snapshot (`@Volatile`).
6. Lookups use a per-statement `HashMap<rule, Set<action>>`. To keep the full-scan hot path cheap, cache rule hashCodes by wrapping keys in an `IdentityHashMap` first, then falling back to the equals map. Measure before optimizing.

**`JIRAnalysisManager` changes:**
- Constructor param `val markSetRecorder: MarkSetRecorder? = null`.
- `private val selectedConfig = SelectedTaintRulesProvider(taintConfig)`, passed to `JIRTaintAnalysisContext` (line ~134). `JIRLocalAliasAnalysis` keeps the raw `taintConfig`.
- `selectPhase`:
  - `Prescan`: `markSetRecorder?.active = true`, `selectedConfig.select(null, emptySet())`.
  - `FullScan`: `markSetRecorder?.active = false`, then the existing `selectRules`.
- `override fun markSetRecorder() = markSetRecorder`.
- `override fun selectStatementRules(...) = selectedConfig.select(...)`.

- [ ] **Step 1: failing provider tests.** Use a fake delegate returning fixed rules for statements s1 and s2.
  - `null` selection: output equals the delegate's.
  - A statement not covered: output equals the delegate's.
  - A covered statement with a sink selected: kept. A covered statement with the sink absent: dropped.
  - A source with 2 actions and 1 selected: the copy has 1 action. With 0 selected: dropped.
  - **G5:** `sinkRulesForMethodExit` with a non-empty `initialFacts`, delegate = `JIRMethodExitRuleProvider(fake)`. Must return empty even when the exit sink is selected.
  - `allRelevant = true`: delegate output.
  - Cleaners and pass-throughs: delegate output.
- [ ] **Steps 2–4:** red, implement, green. Run `./gradlew :opentaint-dataflow-core:opentaint-jvm-dataflow:test --tests '*SelectedTaintRulesProviderTest' --offline -x :opentaint-ir:go:buildGoServer`.
- [ ] **Step 5:** commit `feat(core, analyzer): Add statement-level rule selection with filter semantics`.

### Task 5: Prescan recording hooks (JVM)

**Files:** `TaintAnalysisUnitRunner.kt`, `JIRTaintAnalysisContext.kt`, `JIRMethodSequentFlowFunction.kt`, `JIRMethodCallFlowFunction.kt`, and the new `MarkSetRecording.kt` (jvm-dataflow). Test: root `src/test/kotlin/org/opentaint/jvm/sast/dataflow/MarkSetRecorderSampleTest.kt`, plus a new sample `core/samples/src/main/java/test/samples/MarkSetSample.java`.

**Hooks:**

1. **Edges.** In `TaintAnalysisUnitRunner.subscribeOnMethodSummaries(edge: Edge.ZeroToZero, methodEntryPoint)`, add at its start:
   ```kotlin
   (analysisManager as? TaintAnalysisManager)?.markSetRecorder()?.recordEdge(edge.methodEntryPoint.method, edge.statement, methodEntryPoint.method)
   ```
   Lambda edges take the same path (the engine report confirmed it).
2. **Sites.** In `JIRTaintAnalysisContext`, `prepareCallStatementRules`, `prepareMethodRules` and `sourceRulesForStaticField` gain a `recordMarkSet(statement, list)` call before `handlePhase()`. It sits in `MarkSetRecording.kt` as a `JIRTaintAnalysisContext` extension:
   - It no-ops unless `analysisContext.analysisManager.markSetRecorder()?.active == true`.
   - It calls `recorder.recordStatement(statement)`.
   - Then, per `RuleWithCondition`:

   | Rule | Recording |
   |---|---|
   | `TaintConfigurationSource` | `recordSite(stmt, rule, SOURCE, cond, rule.actionsAfter.map { it.mark.name })` |
   | `TaintConfigurationSink` | `recordSite(stmt, rule, SINK, cond, rule.trackFactsReachAnalysisEnd.map { it.mark.name })` |
   | `TaintPassThrough` | `recordSite(stmt, rule, PASS_THROUGH, cond, emptyList())` |
   | `TaintCleaner` | `recordCleaner(stmt, cond)` |
3. **Exit rules at throws (G6).** In `JIRMethodSequentFlowFunction.propagateZeroToZero`, when `currentInst is JIRThrowInst`, the phase is `Prescan`, and a recorder is present and active, call `analysisContext.taint.sourceRulesForMethodExit(currentInst, null)` and `sinkRulesForMethodExit(currentInst, null, null)`. The results are discarded; the call only records.
4. **Cleaners and pass-throughs at zero call edges (G4).** In `JIRMethodCallFlowFunction.propagateZeroToZero`, under the same Prescan and recorder gate, call `taintCtx.cleanRulesForCallStatement(statement, callExpr, returnValue, null)` and `passRulesForCallStatement(...)` with fact `null`. Discard the results. Check the exact argument names in that file.

- [ ] **Step 1: failing sample test.** `MarkSetSample.java` has:
  - a virtual call;
  - a lambda call;
  - a static-field read;
  - a method that throws, whose exit sink is declared with `methodExitSinkRule`;
  - a cleaner call;
  - two entry points sharing a callee.

  The test uses the `AnalysisTest` style (`runAnalysis` with `markSetScan` on) and exposes the sealed `MarkSetInput` through a test hook. `JIRTaintAnalyzer` stores the last sealed input in `var lastMarkSetInput` (internal, test-visible). Assert:
  - the edges include caller → virtual target and caller → lambda body;
  - a site exists for the exit sink at the `throw` statement;
  - the cleaner atoms include the cleaner's mark;
  - the entry-point source is recorded at the entry statements of non-entry methods;
  - `coveredStatements` contains the throw statement.
- [ ] **Steps 2–4:** red, implement, green. This task depends on Task 6 for `runAnalysis` with the flag. Implement Tasks 5 and 6 together if that is simpler, and keep the commits separate.
- [ ] **Step 5:** commit `feat(core, analyzer): Record the mark-set program during the prescan`.

### Task 6: Phase wiring, options, fail-open, CLI

**Files:** `TaintAnalyzerOptions.kt`, `TaintAnalyzer.kt`, new `MarkSetPhase.kt` (sast-dataflow), `JIRTaintAnalyzer.kt`, `CommonAnalysisOptions.kt`, `ProjectAnalyzerRunner.kt`, `TaintAnalysisUnitRunnerManager.kt` (M7). Test: root `src/test/.../MarkSetPhaseTest.kt`.

**Interfaces:**
```kotlin
data class MarkSetScanOptions(
    val enabled: Boolean = false, val relaxed: Boolean = false, val relevance: Boolean = true,
    val flowSensitive: Boolean = false, val timeLimit: Duration = 30.seconds,
    val maxSites: Int = 20_000_000, val maxEdges: Int = 20_000_000, val debugChecks: Boolean = false,
)
// TaintAnalyzerOptions: val markSet: MarkSetScanOptions = MarkSetScanOptions()
sealed interface MarkSetOutcome {
    data class Selected(val rules: ActionableRules, val covered: Set<CommonInst>, val stats: MarkSetStats) : MarkSetOutcome
    data class FailOpen(val reason: String) : MarkSetOutcome
}
fun runMarkSetPhase(recorder: MarkSetRecorder, roots: Collection<CommonMethod>, prescanOk: Boolean,
                    storeSummaries: Boolean, options: MarkSetScanOptions): MarkSetOutcome
```

**Wiring in `TaintAnalyzer.analyzeStaged`:**
- `prescan` returns `prescanOk = (runCatching succeeded) && ifdsEngine.status.get() == OK`.
- Then, if `analysisManager.markSetRecorder()` is non-null:
  - `outcome = runMarkSetPhase(...)`;
  - log one INFO line per phase (spec §10 Logging), with `markset: time=…ms methods=… edges=… sites=… signatures=… roots=… applicableSinks=… neededMarks=… selectedActions=…/baselineActions=…` or `markset: fail-open (<reason>)`;
  - `Selected` → `analysisManager.selectStatementRules(rules, covered)`.
- `fullScan` is unchanged.

**`runMarkSetPhase` fail-open order** (spec §6.6):
1. `!prescanOk` → `"prescan incomplete"`
2. `storeSummaries` → `"stored summaries"`
3. `recorder.overflow` → `"recorder cap"`
4. `recorder.active = false`, then seal.
5. Run `MarkSetScan` under a time limit: `checkCancelled` throws when elapsed > limit → `"time limit"`.
6. `OutOfMemoryError` → `"memory"`.

**Result → `ActionableRules`:**
- For each applicable site i, with `ref = input.sites[i]`:
  - sink: `rules[ref.statement][ref.rule] = emptySet()`;
  - source: the `AssignMark`s in `rule.actionsAfter` whose `mark.name` has an id in `needed` (or all of them if `!relevance`). A non-empty action set is merged by union.
- Pass-through sites are not emitted, because they are never restricted.
- `baselineActions` = the number of `AssignMark` actions over all recorded source sites, for the log.

**CLI:**
- In `ProjectAnalyzerRunner`, add the options `--mark-set-scan`, `--mark-set-relaxed`, `--mark-set-no-relevance` and `--mark-set-flow-sensitive` as `.flag()`.
- Map them in `CommonAnalysisOptions` (a new field `markSet: MarkSetScanOptions`) and in `taintAnalyzerOptions()`.

**M7:** in `TaintAnalysisUnitRunnerManager` (around lines 115–117 and 487–489), call `updateFailureStatus(...)` *before* `analysisCompletion.complete*`.

**`JIRTaintAnalyzer`:** `analysisManager()` passes `markSetRecorder = if (options.markSet.enabled) MarkSetRecorder(options.markSet.maxSites, options.markSet.maxEdges) else null`.

- [ ] **Step 1: failing tests** (`MarkSetPhaseTest`, root `:test`, using `AnalysisTest` with the flag):
  - On `SimpleDataFlowSample`, the flag on produces the same finding set as off, and the log/outcome is `Selected`.
  - An unrelated rule whose sink never fires: the outcome's `rules` contains none of its source statements. This is the D4 relevance effect end-to-end.
  - `runMarkSetPhase(prescanOk = false)` gives `FailOpen("prescan incomplete")`.
  - `storeSummaries = true` gives `FailOpen("stored summaries")`.
  - A recorder cap of 1 gives `FailOpen("recorder cap")`.
- [ ] **Steps 2–4:** red, implement, green.
- [ ] **Step 5:** commit `feat(core, analyzer): Wire the mark-set phase between prescan and full scan`.

### Task 7: Differential Layer 3 and the spec's new samples

**Files:**
- `src/test/.../jvm/sast/dataflow/AnalysisTest.kt` and `opentaint-java-querylang/src/test/.../util/TestAnalysisRunner.kt`: differential switch.
- `core/build.gradle.kts` and `opentaint-java-querylang/build.gradle.kts`: `systemProperty("opentaint.markset.diff", project.findProperty("marksetDiff") ?: "false")` on the `Test` tasks.
- New samples `core/samples/src/main/java/test/samples/MarkSetDiffSamples.java`, with test `MarkSetDifferentialTest.kt`.

**Switch.** When `System.getProperty("opentaint.markset.diff") == "true"`:
- `runAnalysis` / `run` run twice: baseline, then `markSet = MarkSetScanOptions(enabled = true)`.
- Assert the set of `(vulnerability.ruleId, vulnerability.statement)` is equal between the runs.
- Return the baseline result.

**New samples** (spec §8 Layer 3), each asserting identical findings between the two modes, plus the stated extra:

| Sample | Extra assertion |
|---|---|
| D1: two entry points, shared callee, conjunctive sink over two args | the sink fires in both modes |
| G1: sink with `trackFactsReachAnalysisEnd` | — |
| G4: mark-conditioned cleaner on a field tree holding a needed mark | — |
| G5: exit sink on a fact-to-fact edge | baseline finding count equals mark-set's |
| G6: exit source at a throw | — |
| D4: rule chain source → transformer → sink, plus an unrelated rule | the unrelated rule's source actions are absent from the selection |

- [ ] **Step 1:** write the samples and `MarkSetDifferentialTest` (red until the harness supports both modes).
- [ ] **Step 2:** implement the switch.
- [ ] **Step 3:** run the full differential suites:
  ```
  ./gradlew :test --tests 'org.opentaint.jvm.sast.dataflow.*' -PmarksetDiff=true --offline -x :opentaint-ir:go:buildGoServer
  ./gradlew :opentaint-java-querylang:test -PmarksetDiff=true --offline
  ```
  Expected: every JVM test passes. Any diff is a bug. Investigate it with superpowers:systematic-debugging and **do not** loosen the assertion. The 52 Go failures are the environmental baseline.
- [ ] **Step 4:** commit `test(core, analyzer): Run JVM taint suites differentially under the mark-set selection`.

### Task 8: Option 3* (flow-sensitive, context-insensitive within a root)

**Files:**
- create `markset/FlowSensitiveScan.kt` and `markset/FlowSensitiveScanTest.kt`;
- extend `MarkSetProgram` with an optional `cfg: MethodCfg?`;
- the recorder records statement indices and the site statement index;
- `MarkSetPhase` builds the CFG from the analysis graph at seal time.

**Interfaces:**
```kotlin
class MethodCfg(val stmtCount: IntArray,                 // per method
                val succ: Array<Array<IntArray>>,        // method -> stmt -> successor stmts (normal edges)
                val entry: IntArray, val exits: Array<IntArray>,
                val siteStmt: IntArray,                  // site index -> stmt index in its method
                val callsAt: Array<Array<IntArray>>)     // method -> stmt -> callees
object FlowSensitiveScan { fun run(p: MarkSetProgram, options: MarkSetOptions, checkCancelled: () -> Unit): MarkSetResult }
```

**Semantics.** This is `InFS` from the Lean `FlowSensitive` module, per root, at the method graph level:
- marks flow along `succ`;
- a call point's set flows into the callee's entry;
- the callee's exit sets flow into the successors of reachable call points;
- gens apply at the site's point (single cubes on the root's point set; joined and sink cubes on the union over roots at that point);
- iterate to a fixpoint as a worklist over (root, method, stmt).

`Applicable` = `ApplicableFS`, and `Needed` = `NeededOver(ApplicableFS)`. This is proved exact (`markset_exact_fs`).

**Cost guard:** if `roots × points > 50M`, return `FailOpen("flow-sensitive size")` via the phase.

- [ ] **Step 1: failing tests.**
  - `fs_strict`: a sink before a source in one method (FI applicable, FS not).
  - `linear_order_unsound` loop: the sink at pc1, the source at pc2, back edge 2 → 1. FS must select it.
  - FS applicability ⊆ FI applicability on every oracle program: use the oracle programs with a straight-line CFG in pc order, as the Lean oracle builds them.
- [ ] **Steps 2–4:** red, implement, green. The phase uses `FlowSensitiveScan` when `options.markSet.flowSensitive`.
- [ ] **Step 5:** commit `feat(core, analyzer): Add the flow-sensitive mark-set scan (option 3*)`.

### Task 9: E1/E2 debug checks

**Files:** `MarkSetRecorder.kt` (observer mode), `MarkSetPhase.kt`, and the tests.

**Behaviour:** when `debugChecks` is on, the recorder keeps recording during `FullScan` into separate `observedEdges` and `observedSites` sets. After the full scan, `TaintAnalyzer` calls `recorder.checkCoverage()`. It returns the violations: full-scan edges not in the prescan set (E1), and full-scan `(statement, rule, MarkCond)` triples at covered statements not recorded in the prescan (E2).

- [ ] **Step 1:** in the differential mode of Task 7, turn `debugChecks` on and assert the violations are empty for every test.
- [ ] **Steps 2–4:** red, implement, green. Run both differential suites again.
- [ ] **Step 5:** commit `test(core, analyzer): Check prescan coverage of full-scan edges and rules`.

### Task 10: Conductor experiment

Out of TDD. Record the results in `docs/markset-conductor-experiment.md`.

1. Build the jar: `cd core && ./gradlew :projectAnalyzerJar --offline -x :opentaint-ir:go:buildGoServer`, then copy the jar to the scratchpad.
2. Adapt `cond-ab.sh`: set its `S` to this session's scratchpad, and add an extra-args parameter passed through to the jar.
3. Runs (16G heap as in memory notes; 3 rounds, alternating):
   - baseline: no flag;
   - `--mark-set-scan`;
   - optionally `--mark-set-scan --mark-set-relaxed`;
   - optionally `--mark-set-scan --mark-set-flow-sensitive`.
4. Parse from `analyzer.log`:
   - prescan time (`Start prescan phase` → `Finish prescan phase`);
   - mark-set phase time and stats (the `markset:` line);
   - full-scan time (`Start full scan phase` → `Finish full scan phase`);
   - `Analysis done in` for both phases;
   - the final `Progress:` event counts;
   - the SARIF result count.
5. Compare findings keyed by `(ruleId, path, startLine, startColumn)` (the code-flow key caveat), and report code-flow deltas separately.
6. Report: shallow-scan time (absolute, and as % of prescan), selected/baseline actions and sinks, full-scan time and events (baseline vs mark-set), and finding equality.

---

## Self-review against the spec

| Spec section | Covered by |
|---|---|
| §4 inputs | Tasks 3 and 5, including the G6 throw and G4 cleaner gaps |
| §4.1 α | Task 3 |
| §6.1 / §6.5 algorithm | Task 2 |
| §6.2 4* | Task 2 (relaxed flag, ⊇ oracle) |
| §6.3 relevance | Task 2 |
| §6.4 selection | Tasks 4 and 6 |
| §6.6 fail-open | Task 6 |
| §7 E1 / E2 | Task 9 |
| §7 E0 | Task 3 |
| §7 E4 / E5 / E8 | Tasks 3 and 5, and the Task 7 G4 sample |
| §8 Layers 1–3 | Tasks 1, 2 and 7 |
| §8 Layer 4 | Task 10, Conductor only for now |
| §9 3* (context-insensitive within a root) | Task 8 |
| §9 O-FS-1 / O-FS-2 (context-sensitive 3*) | not implemented: gated by the spec |
| §10 integration, CLI, M7 | Tasks 4 and 6 |

Conductor is the only Layer 4 project, as requested. ThingsBoard and the `known-projects` corpus remain open.

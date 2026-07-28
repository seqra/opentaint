# Separating `cleanAccessors` from `DeepMarkExclusion`

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make a plain sanitizer and a starred sanitizer use one mechanism each — path clearing for `clean($A)`, deep exclusion for `clean($*A)` — and give the deep exclusion the same provenance a path clear already carries.

**Architecture:** `TaintCleanActionEvaluator.removeFinalFact` currently runs both mechanisms on a starred position and lets the fact's *shape* decide how deep the clean reaches. It is split into two branches selected by the position: `arg(0)` (and any concrete path) keeps `cleanAccessors`; `arg(0).[any]` gets a deep branch that filters the fact and records a `DeepMarkExclusion`. The exclusion carries the rule and action that produced it, the way `EvaluatedCleanAction.ActionInfo` already does for a path clear.

**Tech Stack:** Kotlin, JUnit 5, Gradle. The Gradle root is `core/` — the wrapper is `core/gradlew` and every task is invoked from `core/`.

## Global Constraints

- The Gradle root is `core/`. Run `./gradlew` from `core/`, never from the repository root. `:test` is the JVM SAST suite; `:opentaint-dataflow-core:opentaint-dataflow:test` is the dataflow unit suite.
- Baseline at the start of this plan: `:test` **902 passed / 0 failed / 73 skipped**; `:opentaint-dataflow-core:opentaint-dataflow:test` **134 / 0 / 0**. No task may reduce the passing count or add a skip that is not named in that task.
- `DeepMarkExclusion` is exclusion-set-only. Six call sites assert it never appears in an access path (`AccessTree`, `AccessPath`, `AccessCactus`, `AccessPathWithCycles`, `AccessGraphInitialFactAp`, `AccessGraphFinalFactAp`, `AccessorInterner`, `AutomataFactFilter`, `JIRFactTypeChecker`). None of them may be relaxed.
- `ExclusionSet.union` rejects deep entries (`f52cd9a3f`). Nothing this plan adds may route a deep entry into it. `union` composes refinements; a deep entry is not a refinement.
- `ExclusionSet.mergeAndIntersectDeep` intersects deep entries. That law stands: the join of a cleaned and an uncleaned lineage is uncleaned.
- Summary storages keep ONE exclusion per (initial AP, exit AP) (`ba79279ef`). Do not reintroduce per-lineage grouping.
- Every new assertion that a finding is ABSENT must be accompanied by a control that produces it — same program, same sink, cleaner rule deleted. This is the rule that exposed three vacuous Automata passes in `b6eaf34e5`.
- Automata and Cactus have transport gaps unrelated to this work (a call resolving into the analysis unit drops the fact). Do not enable a case in those modes to "prove" a fix; check the mode's control first.

---

## Background an implementer needs

Read this before Task 1. None of it is derivable from the code alone.

**Two mechanisms, today both fire.** `removeFinalFact` (`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/taint/Cleaner.kt`) receives one clean action at a time. A starred sanitizer `clean($*A)` is compiled to TWO actions — `arg(0)` and `arg(0).*` — so the method is called twice. On the `arg(0).*` call it currently does both of:

1. `fact.excludeDeep(markRestriction)`, gated on `fact.factAp.containsAbstractNode()`
2. `cleanAccessors(from.accessorList() + markRestriction, ...)`, gated on `containsPositionWithTaintMark`

**What each mechanism actually is.**

- A *plain* exclusion is partition-backed: the excluded refinement is re-analysed as its own initial fact, so the entry only records "this refinement is carried by another edge". `cleanAccessors` produces those, and it produces an `EvaluatedCleanAction.ActionInfo(rule, action)` alongside.
- A *deep* exclusion is exempt from the partition system — its refinement would need unbounded unrolling — so it is a genuine must-clean claim. It carries no provenance today.

**Where the deep exclusion currently travels, and why that matters.** `excludeDeep` writes the *reader's refinement*, not the fact. `JIRMethodCallFlowFunction.propagateCleanedFact` (line ~205) then does `originalFactReader.updateRefinement(listOf(factReaderAfterCleaner))`, which moves that refinement onto the CALLER's ORIGINAL fact — not onto the cleaned one. A previous attempt that put the claim on the cleaned fact instead regressed three `DeepCleanSummaryAnalysisTest` cases into false negatives. **Which fact owns the claim is the open design question of this plan, and Task 2 answers it by measurement before Task 3 changes anything.**

**Provenance is a presence flag, not a record.** `EvaluatedCleanAction.ActionInfo` has exactly one reader: `JIRMethodCallFlowFunction.kt:179-182`, on the fully-cleaned branch only, where it becomes `TraceInfo.Rule`. Downstream, `VulnerabilityChecker.kt:207-212` matches only its TYPE (`is TraceInfo.Rule`) and never reads `rule` or `action`. So provenance must be *present* where a clean happened; its contents are not yet consumed. Do not build machinery for consumers that do not exist.

**The bug this fixes, in one line.** A starred cleaner applied INLINE does not clear a concrete mark at any depth ≥ 1, while the same cleaner reached through a ladder clears at every depth. The clean's reach is decided by the fact's shape, because `excludeDeep` is gated on `containsAbstractNode()` and path clearing has no depth range at all.

**Red cases this plan turns green** (all `@Disabled` today, all with passing non-vacuity controls):

| file | case | mode |
| --- | --- | --- |
| `AssignmentFormCleanAnalysisTest` | `an assignment-form clean clears the value it returns` | Tree |
| `AssignmentFormCleanAnalysisTest` | `a starred assignment-form clean clears a field of the value it returns` | Tree |
| `AnyFieldMonotonicityAnalysisTest` | `a starred cleaner applied inline clears a concrete mark below the base` | Tree |

---

## File structure

| file | responsibility after this plan |
| --- | --- |
| `.../dataflow/taint/Cleaner.kt` | dispatch on the position; `cleanAccessors` for a concrete path, a new deep branch for `base.[any]` |
| `.../dataflow/taint/FactReader.kt` | `excludeDeep` removed; the refinement channel carries plain accessors only |
| `.../ap/ifds/Accessors.kt` | `DeepMarkExclusion` gains provenance |
| `.../dataflow/taint/EvaluatedCleanAction.kt` | unchanged; `ActionInfo` is reused, not replaced |
| `core/src/test/.../dataflow/DeepExclusionProvenanceTest.kt` | new: provenance survives the merge laws |
| `core/src/test/.../dataflow/CleanerLineageProbeTest.kt` | new in Task 2, deleted in Task 5 |

---

### Task 1: Pin the current dispatch before changing it

A characterization test, so Task 3's diff is readable. No production change.

**Files:**
- Create: `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/CleanerMechanismDispatchTest.kt`

**Interfaces:**
- Consumes: `AnalysisTest` (`assertReachable`, `assertNotReachable`, `functionMatcher`, `sinkRule`), `test.samples.AssignmentFormCleanSample`, `test.samples.AnyFieldChainMonotonicitySample`
- Produces: nothing later tasks import

- [ ] **Step 1: Write the test**

Four cases on Tree, each with its control. Two are green today and must stay green; two are red today and are `@Disabled` with the reason. Use `AnyFieldChainMonotonicitySample` for the depth cases (it has a four-level chain) and `AssignmentFormCleanSample` for the assignment form.

The cases:
1. a plain cleaner `clean($A)` clears the mark at the base and leaves it one level down — green
2. a starred cleaner reached through a ladder clears at depths 0..3 — green
3. a starred cleaner applied inline clears at depth 0 — green
4. a starred cleaner applied inline clears at depths 1..3 — **red**, `@Disabled`

Every "clears" assertion is preceded by the same assertion with the cleaner rule deleted, which must report.

- [ ] **Step 2: Run**

```
./gradlew --offline :test --tests '*CleanerMechanismDispatch*'
```

Expected: 3 passed, 1 skipped, 0 failed.

- [ ] **Step 3: Commit**

```bash
git add core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/CleanerMechanismDispatchTest.kt
git commit -m "test(dataflow): pin which mechanism each cleaner flavour uses today"
```

---

### Task 2: Measure which fact must own the deep claim

**This task changes no production code and ships no permanent test.** It answers the open question from the Background so Task 3 is not a guess. A previous attempt skipped this and regressed three cases.

**Files:**
- Create: `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/CleanerLineageProbeTest.kt` (temporary; Task 5 deletes it)
- Read: `.../jvm/ap/ifds/analysis/JIRMethodCallFlowFunction.kt` lines 160-230

- [ ] **Step 1: Instrument**

Add temporary `println` (or a file appender under the scratchpad) at three points, and run `TreeDeepCleanSummaryAnalysisTest` plus `TreeAssignmentFormCleanAnalysisTest`:

- in `removeFinalFact`, on entry: the position, the mark, `fact.factAp` and its exclusions
- in `propagateCleanedFact`, before and after `originalFactReader.updateRefinement(...)`: both readers' facts and refinements
- at each `Sequent` construction in `MethodCallSummaryHandler.handleSummary`: the initial fact, the final fact and the exclusion

- [ ] **Step 2: Answer three questions in writing**

Record answers in `docs/superpowers/reports/2026-07-28-deep-claim-ownership.md`:

1. For `wrap` in `DeepCleanSummarySample`, which summary edges exist after `clean(b)`, and which of them carries the deep exclusion when the tests are green today?
2. Does the cleaned fact reach the summary storage at all, or only the original fact refined by `updateRefinement`?
3. If the deep exclusion is placed on the cleaned fact instead, which edge loses it — and is that why `unsanitized sibling edge from the same initial fact stays reported` flipped to a false negative in the earlier attempt?

- [ ] **Step 3: Choose**

State one sentence in the report: **the deep claim is owned by X**, where X is either the cleaned fact, the original fact's refinement, or both. Task 3 implements exactly that. If the measurement says the current placement is already correct, Task 3 keeps it and only adds provenance.

- [ ] **Step 4: Remove the instrumentation and commit the report**

```bash
git checkout core/opentaint-dataflow-core
git add docs/superpowers/reports/2026-07-28-deep-claim-ownership.md
git commit -m "docs(dataflow): measure which fact owns a deep mark exclusion"
```

Expected: `git diff HEAD -- core/opentaint-dataflow-core` is empty.

---

### Task 3: Give `DeepMarkExclusion` provenance

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/ap/ifds/Accessors.kt` (the `DeepMarkExclusion` declaration, ~line 100)
- Modify: `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/JIRSummariesFeature.kt` (lines ~205, ~254, ~383 — serialization)
- Test: `core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/ap/ifds/ExclusionSetDeepMergeTest.kt`

**Interfaces:**
- Consumes: `EvaluatedCleanAction.ActionInfo(rule: CommonTaintConfigurationItem, action: CommonTaintAction)`
- Produces: `DeepMarkExclusion(mark: String, origin: ActionInfo?)`, where `origin` is excluded from `equals`/`hashCode`/`compareTo`

- [ ] **Step 1: Write the failing test**

In `ExclusionSetDeepMergeTest`:

```kotlin
@Test
fun `provenance does not affect identity`() {
    // Two lineages clean the same mark under different rules. They must still intersect to a
    // non-empty deep set -- if provenance entered equality, every join would drop every entry.
    val fromRuleA = DeepMarkExclusion("m", originA)
    val fromRuleB = DeepMarkExclusion("m", originB)

    assertEquals(fromRuleA, fromRuleB)
    assertEquals(fromRuleA.hashCode(), fromRuleB.hashCode())
    assertTrue(fromRuleA in setOf(fromRuleB).mergeAndIntersectDeep(setOf(fromRuleA)))
}

@Test
fun `provenance survives a lineage join that keeps the entry`() {
    val merged = setOf(DeepMarkExclusion("m", originA)).mergeAndIntersectDeep(setOf(DeepMarkExclusion("m", originB)))

    assertTrue(merged.deepExclusion().single().origin != null)
}
```

`originA`/`originB` are two `ActionInfo` values built from distinct cleaner rules.

- [ ] **Step 2: Run to verify it fails**

```
./gradlew --offline :opentaint-dataflow-core:opentaint-dataflow:test --tests '*ExclusionSetDeepMerge*'
```

Expected: compilation failure — `DeepMarkExclusion` takes one argument.

- [ ] **Step 3: Add the field**

```kotlin
data class DeepMarkExclusion(val mark: String) : Accessor() {
    /**
     * The clean action that established this claim, mirroring [EvaluatedCleanAction.ActionInfo] on
     * a path clear. Deliberately outside identity: two lineages that clean the same mark under
     * different rules must still intersect to a non-empty deep set.
     */
    var origin: ActionInfo? = null
        private set

    fun withOrigin(origin: ActionInfo): DeepMarkExclusion = DeepMarkExclusion(mark).also { it.origin = origin }
```

Keep `equals`, `hashCode` and `compareToDeepMarkExclusion` on `mark` alone — `data class` generates them from the constructor parameter, which is why `origin` is a body property rather than a second parameter.

Serialization in `JIRSummariesFeature` writes and reads `mark` only; a deserialized entry has `origin == null`. Add a one-line comment saying so.

- [ ] **Step 4: Run**

Expected: PASS. Then the full dataflow unit suite, expected 136/0/0 (134 + 2 new).

- [ ] **Step 5: Commit**

```bash
git add core/opentaint-dataflow-core
git commit -m "feat(dataflow): a deep mark exclusion records the action that made it"
```

---

### Task 4: Split the two mechanisms

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/taint/Cleaner.kt`
- Modify: `core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/taint/FactReader.kt`
- Test: the three cases listed in the Background table

**Interfaces:**
- Consumes: `DeepMarkExclusion.withOrigin` from Task 3, the ownership decision from Task 2
- Produces: no new public API

- [ ] **Step 1: Un-disable the three red cases**

Remove the `@Disabled` from the three cases in the Background table. Run and confirm they fail — 3 failed, and the counts otherwise match the baseline.

- [ ] **Step 2: Dispatch on the position**

In `removeFinalFact`, replace the two-mechanisms-both-fire body with a branch:

```kotlin
if (from.isBaseAnyFieldPosition()) {
    return deepCleanMark(fact, markRestriction, rule, action, evc)
}

if (!fact.containsPositionWithTaintMark(from, markRestriction)) return listOf(evc)
return cleanAccessors(from.accessorList() + markRestriction, fact, rule, action, evc)
```

`isBaseAnyFieldPosition()` already exists and is exactly the test — keep it.

- [ ] **Step 3: Implement the deep branch**

Two halves, covering disjoint parts of the fact:

- **Concrete occurrences are cut.** `factAp.filterFact(filter)` where the filter rejects the mark accessor at every depth:

```kotlin
private class DropMarkFilter(private val mark: TaintMarkAccessor) : FactTypeChecker.FactApFilter {
    override fun check(accessor: Accessor): FactTypeChecker.FilterResult =
        if (accessor == mark) FactTypeChecker.FilterResult.Reject else FactTypeChecker.FilterResult.FilterNext(this)
}
```

`filterFact` returns `null` when nothing survives — that is the fully-cleaned case and yields `EvaluatedCleanAction(fact = null, ActionInfo(rule, action), evc)`.

- **Abstract depths get the claim.** Add `DeepMarkExclusion(mark.mark).withOrigin(ActionInfo(rule, action))` to whichever fact Task 2 named. `ExclusionSet.Universe.add` is a no-op, which correctly means "this fact is exact, filtering it was the whole clean".

Emit an `ActionInfo` whenever either half changed something; return `listOf(evc)` unchanged when neither did.

- [ ] **Step 4: Remove `excludeDeep`**

Delete `FinalFactReader.excludeDeep` and its `DeepMarkExclusion` import. The refinement channel now carries plain accessors only, which is what `ExclusionSet.union`'s check already assumes.

- [ ] **Step 5: Run the three cases**

```
./gradlew --offline :test --tests '*AssignmentFormClean*' --tests '*AnyFieldMonotonicity*'
```

Expected: the three previously-red cases PASS.

- [ ] **Step 6: Run everything**

```
./gradlew --offline :test :opentaint-dataflow-core:opentaint-dataflow:test
```

Expected: `:test` **905 passed / 0 failed / 70 skipped** (902 + 3 un-skipped), dataflow **136 / 0 / 0**.

If `DeepCleanSummaryAnalysisTest` regresses, the ownership decision from Task 2 was wrong — return to Task 2's report rather than patching around it. Those cases are false negatives, the worst direction, and must not be disabled to make this task pass.

- [ ] **Step 7: Commit**

```bash
git add core/opentaint-dataflow-core core/src/test
git commit -m "fix(dataflow): a starred sanitizer cleans by deep exclusion, a plain one by path"
```

---

### Task 5: Provenance reaches a trace, and cleanup

**Files:**
- Modify: `core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/analysis/JIRMethodCallFlowFunction.kt` (lines ~176-182)
- Create: `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/DeepExclusionProvenanceTest.kt`
- Delete: `core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/CleanerLineageProbeTest.kt` if Task 2 left it

**Interfaces:**
- Consumes: `DeepMarkExclusion.origin` from Task 3
- Produces: nothing

- [ ] **Step 1: Write the test**

A starred cleaner that fully clears a flow must produce a `TraceInfo.Rule`, exactly as a plain one does. Assert on the trace the analysis reports, using `AssignmentFormCleanSample.cleanedFlow` — where a plain and a starred cleaner both fully clear.

If the existing test helpers cannot observe traces, assert instead that the deep exclusion on the summary edge has a non-null `origin`, and say in a comment why the trace itself is not reachable from the test API.

- [ ] **Step 2: Run to verify it fails**

- [ ] **Step 3: Carry the origin into the trace**

At the `cleanerResult.fact == null` branch, the `ActionInfo` is already present and needs no change. Where a starred clean did NOT fully clear but did establish a claim, take the origin from the deep entry so the branch produces the same `TraceInfo.Rule`. Keep the shape of the existing `takeIf { (it.rule as? TaintConfigurationItem)?.info is UserDefinedRuleInfo }` filter.

- [ ] **Step 4: Run**

Expected: PASS, and `:test` still 905/0/70.

- [ ] **Step 5: Delete the probe and commit**

```bash
git rm -f core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/CleanerLineageProbeTest.kt 2>/dev/null || true
git add -A
git commit -m "feat(dataflow): a whole-object clean reports the rule that cleaned"
```

---

## Out of scope

- **`removeAllFacts`** has the same shape (a `base.[any]` position falls to `cleanAccessors`) and the same gap. It takes no mark restriction, so there is no `DeepMarkExclusion` to record and the fix is not the same fix. Separate plan.
- **The Automata intervening-call gap** — a call resolving into the analysis unit drops the fact. Pinned by `AssignmentFormCleanAnalysisTest`'s controls, deferred by decision. Nothing here makes it better or worse.
- **Cactus.** Loses assignment-form transport almost entirely; class-level disabled.
- **Rule-test validation.** The shipped-rule corpus is not part of `:test`. Run it after Task 4 if the analyzer jar is available, expecting no new FPs; it is not a gate for this plan.

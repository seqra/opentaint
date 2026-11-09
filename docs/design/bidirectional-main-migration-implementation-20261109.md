# Implementation proposal: migrate the bidirectional core to main

9 November 2026. Status: ready for implementation review. No rebase, runtime
patch or new project measurement is part of this document.

Implement [spec/main-migration.md](../../spec/main-migration.md). Follow the
[implementation guide](../../spec/impl-proposal-guide.md) and
[proof guide](../../spec/proof-guide.md). Code below is Kotlin-like pseudocode.
Proposed helpers are identified as such; they are not current public APIs.

Latest reached project iteration: not applicable to this proposal task.

## 1. Versions and delivery order

| Role | Revision |
| --- | --- |
| Proposal source checkout | `0092f410ce5f5e83a7d1a332d9984aba9e57eb39` |
| Specification baseline | `14b8ac8354bfc824080e790c7d71f6cfae0f401a` |
| Shared main base | `f945f92c5ae554ff4f5fc7696ee5a269210478bb` |
| Pinned actual main | `54ad708fe1c4f551956d3d572866de1534415fa1` |

The proposal checkout and specification baseline have the same `core` tree.
The remote main tip was checked again for this proposal. If main advances,
audit the new range and update the pin before implementation.

Use the primary checkout on `saloed/bidirectional`. The delivery order is
**rebase, then adapter changes, then validation**. Preserve the internal
merge topology where needed. Do not create another implementation worktree,
copy an old implementation over main, or resolve a whole directory with
`ours`/`theirs`.

Main supplies its compiler, public rule types, model inputs, model loader,
build changes and legacy/Go changes. The post-rebase edits below make the
existing new-core adapter consume those contracts. The old and new engines
remain available through their current engine-selection boundary.

The planned history operation is shown below; it is not executed by this
proposal task. Resolve conflicts by the file/behavior inventory.

```bash
git rebase --rebase-merges --onto \
  54ad708fe1c4f551956d3d572866de1534415fa1 \
  f945f92c5ae554ff4f5fc7696ee5a269210478bb saloed/bidirectional
```

## 2. Classification and semantic scope

Use exactly these behavior labels in the file inventory:

- **works-as-on-main**: the affected behavior follows pinned main. Examples
  are ActionPosition, explicit starred reach, focused sanitizer generation,
  named model fields and getter fallback.
- **works-as-on-bidir**: the affected behavior keeps the selected branch
  contract. Examples are C2/C5, source-definition reset scope, mark ownership,
  Targets and predefined Spring cleanup. The label also covers branch-owned
  shared provider hooks; it does not mean that Go uses the new core.

These are behavior classifications, not byte-equality claims. One file can
have both labels on separate rows because it joins the two contracts. There
is no third “mixed” policy that can choose either behavior arbitrarily.

### 2.1 Selected semantic changes

| Part | Before | After | Classification / proof |
| --- | --- | --- | --- |
| Rule reach | Array and Spring type checks can add reach | Main compiler positions are the only source of rule reach | works-as-on-main; P01–P07, P14 |
| Serialized AnyField | Accessors after AnyField can reject in the adapter | Main binds only the concrete prefix before its first AnyField | works-as-on-main; P01–P02 |
| Selected cleaner | Some actions also clean String bytes implicitly | Exact and below actions operate only at explicit positions | works-as-on-main; P12/P15 |
| Spring | Provider widens entry sources and exit checks | Starred rules supply reach; controller exit bypass remains | works-as-on-main; P17 |
| Getter | Default rules are appended to explicit rules | Select defaults only if the prepared explicit list is empty | works-as-on-main; P13, I01–I06 |
| Rules/models | Old rules, generic carrier fields, old addressing | Use main's complete compiler/rule/model/loader input set | works-as-on-main; native loading/quality gates |
| Public API | Ordinary Position plus selected-clean `reach` | ActionPosition wrappers; core operations stay the same | works-as-on-main API, works-as-on-bidir primitives; P08–P12 |
| Legacy cap in bidi mode | New main option has no defined branch handling | Ignore it, log once, and clear it from effective shared-engine options | works-as-on-bidir; P16, I12–I14 |

These are declared semantic changes. This migration is not a technical-only
optimization and does not promise the same findings under changed rules/models.

Keep the AP algebra, four tails, FULL default, `1,1,2,3,...` schedule, GROUP
availability/known issues, C2/C5, FLOW companions, protection classes,
subsumption, field transfer, static pools and summary policy, loop gates,
Targets, stopping and current source permissions. A pass still never creates
protection. Keep sink end actions empty. Preserve current rejection of an
AnyField pass input and below-only RemoveAllMarks.

No new store, grounding support, initial kind, legacy unfold filter, alias
policy or extra demand completion is selected.

## 3. File inventory

The [complete CSV inventory](data/bidirectional-main-migration-files-20261109.csv)
lists **657 distinct paths in 691 behavior rows**. Each row has a path,
rename source where applicable, operation, phase, classification, short change
and reason. It includes every one of the audit's 601 imported file changes;
none is hidden behind a directory wildcard. It also lists adapter/test edits
and the proposal/proof/validation artifacts.

| Phase | Inventory rows | Meaning |
| --- | ---: | --- |
| `rebase` | 601 | Changes already supplied by main; do not implement them again |
| `post-rebase` | 79 | Reconcile branch hooks, adapt the new core and update/add native tests |
| `proposal-and-validation` | 11 | This proposal/proof package and later validation evidence |

Counts are planned scope, not a claim that runtime files have been modified.
Some paths have an imported row and an additional branch-behavior row.
`Rnnn` operations retain both exact old/new paths. Reconcile the inventory
against the actual patch before landing; a new runtime path requires an
explicit explanation, not an automatic expansion of scope.

### 3.1 Main adapter edits

The following table shows the principal post-rebase runtime edits. Complete
repository-relative paths and every test/imported file are in the CSV.

| File | Modification and reason | Behavior |
| --- | --- | --- |
| [JIRRuleForms.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRRuleForms.kt) | Add wrapper decoding; remove hidden String-byte work; retain existing source/pass/clean/reset primitives and validation | works-as-on-main for encoding/reach; works-as-on-bidir for primitive execution |
| [JIRRulePredicates.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRRulePredicates.kt) | Remove automatic array leaves; keep current predicate DAG and conjunction handling | works-as-on-main reach; works-as-on-bidir predicate engine |
| [JIRCallPlanBuilder.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/bidi/interp/JIRCallPlanBuilder.kt) | Remove array callback; select getter rules before validation/output filtering; lower source resets directly | works-as-on-main fallback; works-as-on-bidir stages, reset and IDs |
| [JIRTaintAnalyzer.kt](../../core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/JIRTaintAnalyzer.kt) | Sanitize only the ignored legacy cap before shared-engine construction and log the raw request once | works-as-on-bidir |
| [MethodTaintConfigurationResolver.kt](../../core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/rules/MethodTaintConfigurationResolver.kt) | Keep main prefix/wrapper binding and branch per-action cleaner normalization, labels and empty sink end actions | works-as-on-main binding; works-as-on-bidir normalization/selection |
| [TaintConfiguration.kt](../../core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/rules/TaintConfiguration.kt) | Retain resolver views, catalogs and mark reduction around main static-source wrapping | works-as-on-main API; works-as-on-bidir provider policy |
| [StringConcatRuleProvider.kt](../../core/opentaint-jvm-sast-dataflow/src/main/kotlin/org/opentaint/jvm/sast/dataflow/StringConcatRuleProvider.kt) | Use wrapped actions without losing provider/catalog and original-alias-view delegation | works-as-on-main API; works-as-on-bidir delegation |
| [SpringRuleProvider.kt](../../core/src/main/kotlin/org/opentaint/jvm/sast/project/spring/SpringRuleProvider.kt) | Remove widening helpers; keep controller applicability, branch selection and complete cleanup model bypass | works-as-on-main rules; works-as-on-bidir cleanup/ownership |
| [AutomataToTaintRuleConversion.kt](../../core/opentaint-java-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/taint/AutomataToTaintRuleConversion.kt) | Merge main star-aware position/state generation with branch `markPrefix`/`markOwners` | works-as-on-main generation; works-as-on-bidir mark ownership |
| [TaintRuleProcessing.kt](../../core/opentaint-java-querylang/src/main/kotlin/org/opentaint/semgrep/pattern/conversion/taint/TaintRuleProcessing.kt) | Merge main focus/star processing with branch top-level generated-mark ownership | works-as-on-main generation; works-as-on-bidir ownership |
| [JIRLocalAliasAnalysis.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/JIRLocalAliasAnalysis.kt) | Keep original alias-rule lookup; use main Exact-only external-object extraction | works-as-on-main extraction; works-as-on-bidir original rule view |
| [JIRFactTypeChecker.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/JIRFactTypeChecker.kt) | Remove main's obsolete array helper; retain exposed local/field filters used by the adapter | works-as-on-main helper removal; works-as-on-bidir filters |
| [TaintEvaluator.kt](../../core/opentaint-dataflow-core/opentaint-jvm-dataflow/src/main/kotlin/org/opentaint/dataflow/jvm/ap/ifds/taint/TaintEvaluator.kt) | Keep main wrapper helpers and retain rejection of internal JVM rule bases | works-as-on-main public API; works-as-on-bidir base validation |

### 3.2 Shared files which need conflict reconciliation

These are existing branch hooks, not new analysis mechanisms. The CSV lists
each path separately.

| Files | Required reconciliation | Behavior |
| --- | --- | --- |
| Common `TaintAnalyzer`, `TaintAnalysisUnitRunnerManager`, `TaintAnalysisUnitRunner`, `MethodAnalyzer`, `Accessors` | Main legacy cap/AP changes plus branch dispatch, joined prescan export/release and diagnostics | works-as-on-main legacy analysis; works-as-on-bidir dispatch/prescan hooks |
| JVM `JIRAnalysisManager`, `JIRMethodAnalysisContext` | Main context API plus existing joined resolved-graph lifecycle | works-as-on-main legacy context; works-as-on-bidir prescan interface |
| JVM `JIRMethodCallRuleBasedSummaryRewriter` | Main action wrappers plus original action/reset-mark selection | works-as-on-main legacy operation; works-as-on-bidir selection |
| Go `GoAnalysisManager`, `GoCallRuleBasedSummaryRewriter`, `GoTaintConfiguration` | Main Go models/positions plus existing original-row metadata and selection | works-as-on-main Go engine; works-as-on-bidir shared branch selection |
| `CommonAnalysisOptions`, `ProjectAnalyzerRunner`, `core/build.gradle.kts` | Main options/resources plus existing bidi flag and test/measurement properties | works-as-on-main option/build additions; works-as-on-bidir selection |

No post-rebase algorithm change is planned in `bidi/ap`, `bidi/store`,
`bidi/engine` or `bidi/driver`. Main's legacy changes stay in the legacy paths.
The one public-JVM-action fixture in common-core tests needs a constructor
update, not an engine change.

## 4. Canonical wrapper decoding and atomic validation

Keep the current `JIRRuleForms.RulePos`; its `any` bit remains adapter-local.
Do not introduce another public descriptor or store flag.

```kotlin
// Existing class, proposed overloads. Ordinary Position is concrete on main.
fun pos(rule: Any, p: Position): RulePos? =
    concretePosition(rule, p.resolveAp())

fun pos(rule: Any, p: ActionPosition): RulePos? = when (p) {
    is ActionPosition.Exact -> pos(rule, p.position)
    is ActionPosition.AnyAccessorAfter ->
        pos(rule, p.position)?.copy(any = true)
}

private fun concretePosition(rule: Any, p: PositionAccess): RulePos? {
    val accessors = p.accessors()
    if (accessors.any { it === AnyAccessor })
        return rejectPosition(rule, "ordinary JVM positions must be concrete")
    // Existing Return-to-resultBase mapping, static-anchor checks,
    // typed accessor interning and owned immutable path construction.
    return existingConcretePosition(rule, p.base(), accessors)
}

fun literal(rule: Any, l: Literal): PathFact? = when (l) {
    is ContainsMarkLiteral -> pos(rule, l.position)?.fact(fullMark(l.mark))
    is ContainsMarkOnAnyAccessorLiteral ->
        pos(rule, l.position)?.copy(any = true)?.fact(fullMark(l.mark))
}

fun addSourceRule(builder: MicroEdgeBuilder, rule: TaintConfigurationSource) {
    if (!valid(rule)) return // Before ANY builder/static-operation mutation.
    source(builder, rule, originalOccurrence(rule), rewrittenCondition(rule))
}
```

`concretePosition` must support ordinary `PositionAccess` literals as well as
public Position. The main binder already applies first-AnyField normalization;
do not reparse serialized modifiers here. Retain the existing class/anchor,
read-source and complete-raw-rule validation before folding or form mutation.

Source and sink conditions still use signed normalization followed by the
existing approximation. Keep complete AND/OR structure. A rule pattern with
ANY is not an owned analyzer initial. Change no C2 admission to make it fit.

Atomicity is per rejected rule. Default call binding/ZERO preservation can
remain in the surrounding plan; it is not an effect of the rejected rule.
Use existing `valid(rule)` caching rather than a second validation cache.

## 5. Keep the existing primitives

The current `RulePos.fact`, `sourceFact` and `star` already distinguish these
cases. Keep them and their existing mark-mode conversion.

```kotlin
// These are rule templates. Existing execution supplies premises and layers.
Exact(p).sourceFact(T)   == p.EXACT(T)
AnyAfter(p).sourceFact(T) == p.MUST(T)
Exact(p).star()          == p.STAR(FLOW)
AnyAfter(p).star()       == p.MAY(FLOW)

// Keep current pass lowering and its no-new-protection policy.
CopyAllMarks(Exact(p), Exact(q))    -> existingFlowPass(p.STAR, q.STAR)
CopyAllMarks(Exact(p), AnyAfter(q)) -> existingFlowPass(p.STAR, q.MAY)
CopyMark(T, Exact(p), to)           -> existingSelectedMarkPass(T, p, to)

// Keep rejection before lowering.
CopyAllMarks(AnyAfter(p), to) -> rejectWholeRule()
RemoveAllMarks(AnyAfter(p))   -> rejectWholeRule()
```

Keep `forms.pass` static read/write registration at its current micro-edge
seam. Keep source rule IDs, complete source guards and FULL/GROUP projection.
Do not create a write point during call-summary application or force an
Exact static template to NORMAL in run-1.

### 5.1 Selected cleaners and source resets

Remove public `reach` inspection and the String-byte expansion. Add one
small **proposed** `definitionReset` helper in `JIRRuleForms`; reuse its
existing `lowerCleaner` for field temporaries, types and reversal.

```kotlin
fun selectedCleaner(
    rule: TaintConfigurationItem, action: RemoveMark,
    types: PositionTypeResolver, actionId: ActionId?
): CleanStep {
    val p = requireNotNull(pos(rule, action.position))
    val reach = if (p.any) CleanReach.BELOW else CleanReach.EXACT
    return lowerCleaner(Cleaner(p.base, node(p.path), reach, mark(action.mark)),
                        types, actionId?.let(::TemporaryKey))
}

// Proposed. Called only by the existing user-rule return rewriter.
fun definitionReset(
    rule: TaintConfigurationItem, position: ActionPosition, source: Boolean,
    resetMark: RuleMark, types: PositionTypeResolver, actionId: ActionId
): CleanStep {
    val p = requireNotNull(pos(rule, position))
    val reach = when {
        !p.any -> CleanReach.EXACT
        source -> CleanReach.AT_AND_BELOW
        else -> CleanReach.BELOW
    }
    return lowerCleaner(Cleaner(p.base, node(p.path), reach, mark(resetMark)),
                        types, TemporaryKey(actionId))
}

fun allMarksCleaner(rule, action: RemoveAllMarks, types, actionId): CleanStep {
    val p = requireNotNull(pos(rule, action.position))
    require(!p.any) // valid(rule) already checked this.
    return existingWholePositionKill(p, types, actionId)
}
```

`unconditional` still ignores non-clean actions as it does now. Configured
selected cleaners return one step per action, not an added String-byte step.
The whole-position static kill remains the current ordered strong-keep
construction; do not route it through a new all-mark operator.

In `JIRCallPlanBuilder.rewriterSteps`, change
`List<Pair<Int,Position>>` to `List<Pair<Int,ActionPosition>>`. Pass the
original position and `source` flag to `definitionReset`. Keep the existing
metadata condition gates, relevant reset marks, source/cleaner ordinal
offsets and `ActionRole.RETURN_REWRITER`.

Do not encode an at-and-below source reset with one configured AnyAfter clean.
Do not split it into two new runtime rules or restore a public `reach` field.
Keep the existing generated primitive and its field-value temporary identity.

### 5.2 Preserve branch cleaner normalization during binding

Main's resolver returns one cleaner in places where the branch can return
several condition/action groups. Keep the branch's per-action normalization
around main's new action binding.

```kotlin
// Adapt the existing assumption helper; do not specialize metadata guards
// with the executable mark set here.
fun Action.assumedLiterals(): Set<JirCondition> {
    if (this !is RemoveMark) return emptySet()
    return when (val p = position) {
        is ActionPosition.Exact -> setOf(ContainsMark(p.position, mark))
        is ActionPosition.AnyAccessorAfter ->
            setOf(ContainsMarkOnAnyField(p.position, mark))
    }
}

fun bindCleaner(serialized, condition, context): List<TaintCleaner> {
    val actions = serialized.cleans.flatMap { it.resolve(context) } // main API
    return actions.groupBy { condition.assumeAction(it) }
        .filterKeys { !it.isFalse() }
        .map { (guard, selected) -> existingCleanerWithOriginalLabels(guard, selected) }
}
```

The old alias literal `CM(prefix.AnyField,T)` normalizes to the same
`CMAny(prefix,T)` on main. It does **not** become `CM(prefix,T)`. For example,
`p.f/T` can make a below-p clean relevant while p itself has no T. The helper
must not assume a root mark. The supplemental Lean model checks this case
and proves truth preservation when the assumed literal holds.

Keep `ignoreSinkEndFacts`, original resolver views and action ordinal mapping.
Keep metadata binding distinct from executable mark reduction. Do not revive
`resolveWithArray`/`resolveNoArray` or resolve an ignored end-action position.

## 6. Remove automatic array reach

```kotlin
// JIRRulePredicates: proposed reduced signature.
fun compile(condition: ExprOrConstant): RulePredicate {
    // Existing builder, signed preprocessing and iterative DAG walk.
    // At a literal, add exactly the explicit literal supplied by the binder.
    val leaf = builder.leaf(Pattern(literal(node), ExclusionSet.Empty))
    // Delete the mayBeArray test and prefixed ElementAccessor OR arm.
    // Keep AND/OR construction and all existing cancellation checks.
    return existingBuiltPredicate()
}

// JIRCallPlanBuilder.sinks(): no checker.callArgumentMayBeArray callback.
forms.sinks(rule, rewrittenCondition, originalOccurrence)
```

Remove the `mayBeArray` parameters in `JIRRuleForms.fullPredicate`,
`predicate` and `sinks`. Update their existing callers. `JIRBoundaryForms`
already calls the no-callback form; verify it rather than inventing a new
boundary path. Explicit ElementAccessor positions remain legal.

Do not reject a starred Semgrep propagator by its source syntax. Main can
compile it to mark-dependent source rules. Only an actual bound Copy action
with an AnyAfter input is the retained unsupported shape.

## 7. Select default getters before output processing

Use one local prepared vector during `JIRCallPlanBuilder.passRules()`.
Do not cache offered facts or add a global getter-presence index.

```kotlin
// Proposed local build-time record. It does not enter logical edge keys.
data class PreparedPass(val rule: TaintPassThrough,
                        val condition: ExprOrConstant,
                        val originalOrdinal: Int,
                        val fromExplicitSet: Boolean)

val supplied = forms.rules.passTroughRulesForMethod(callee, s, fact = null)
val rows = supplied.toList() // Consume this query once.
val fallbackOffset = if (supplied is SpecializedRules<*>) supplied.originalRuleCount
                     else rows.originalRuleCount() // Before filtering.
val prepared = rows.withIndex().map { (index, rule) ->
    PreparedPass(rule, rewriter.rewrite(rule.condition),
                 rule.ruleOrdinal(index), fromExplicitSet = true)
}.filterNot { it.condition.isFalse }

val selected = if (prepared.isNotEmpty()) prepared else
    defaultGetModel?.defaultPropagationRules(callee).orEmpty()
        .mapIndexed { index, row ->
            PreparedPass(row.rule, row.condition, fallbackOffset + index,
                         fromExplicitSet = false)
        }

for (row in selected) {
    if (!forms.valid(row.rule)) continue // presence decision is already fixed
    if (row.condition.isFalse) continue
    // Keep the existing pass-condition approximation/diagnostic.
    for ((index, action) in row.rule.actionsAfter.withIndex()) {
        val id = originalPassActionId(row.originalOrdinal,
                                     row.rule.actionOrdinal(index))
        val (read, written) = forms.pass(builder, row.rule, action,
                                        OperationId(formKey, action = id)) ?: continue
        reads += read
        writes += written
        if (row.fromExplicitSet) passReads += read
    }
}
// Keep existing operand/result filters and the separate default identity stage.
```

A present but invalid non-false explicit row produces a diagnostic and no
partial rule output. It blocks fallback. A statically false row does not.
A valid row that produces nothing for the offered fact also blocks fallback.
Do not filter by actual fact or successful output before this decision.

Use main's `JIRMethodGetDefault`: the relation reads `<get-default>` on the
declaring class. Its existing array/Object result actions stay explicit.
Forward, backward and reporting use the same managed forward/reverse plan;
do not independently select fallback in the backward or trace path.

## 8. Spring, providers and model loading

```kotlin
override fun entryPointRulesForMethod(method, statement, fact, allRelevant) =
    if (method is SpringGeneratedMethod) emptyList()
    else base.entryPointRulesForMethod(method, statement, fact, allRelevant)

override fun sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant) = when {
    method is SpringGeneratedMethod -> emptyList()
    method is JIRMethod && method.isSpringControllerMethod() ->
        base.sinkRulesForMethodExit(method, statement, fact,
                                   initialFacts = null, allRelevant = allRelevant)
    else -> base.sinkRulesForMethodExit(method, statement, fact, initialFacts, allRelevant)
}

// Retain the current generated-cleanup guard before the legacy compatibility path.
if (method is SpringGeneratedMethod && method.predefinedSummary != null)
    return emptyList() // no legacy cleanup rule or body analyzer
```

Delete `taintObjectFields`, `unfoldSpringExitObject`, their private condition
rewriter and Continuation helper. Keep main's controller annotation matching
and source regex. Wrap repository actions with Exact; do not change their
content field, SAVE/FIND direction or branch stable action labels.

Keep `BidirectionalRulesProviderFactory`, executable-catalog/mark-reduction
delegation, original alias view and complete predefined cleanup summaries.
Do not restore generated static save/restore assignments or a dispatcher exit
sink. NORMAL conditional controller summaries remain valid exit witnesses.

Use main's model module discovery, resource aggregation, prefix/annotation
loader and Go model support from the rebase. No new model discovery layer is
needed in `JIRBidiAnalysis`. Preserve the existing startup order:

```text
load main configuration and model bodies
    -> build IR/model-aware classpath
    -> resolve all calls during joined prescan
    -> build selected provider/catalog and immutable method forms
    -> run the current bidirectional driver
```

Main named virtual fields keep their exact owner/name/type. Do not rename
them back to `<rule-storage>`, add a blanket identity or analyze both an
original external body and its model as independent targets.

## 9. Ignore the legacy cap at the engine boundary

Implement the diagnostic and effective option isolation in `JIRTaintAnalyzer`.
Keep its public `options` named argument and existing `bidiPolicy` selection.
The code below uses the original constructor argument in `init`.

```kotlin
class JIRTaintAnalyzer(
    /* existing parameters */, options: TaintAnalyzerOptions,
    /* existing parameters */, val bidiPolicy: IterationPolicy? = null,
) : TaintAnalyzer<JIRMethod,JIRInst>(
    options = if (bidiPolicy == null) options
              else options.copy(iterationLimit = null),
    externalMethodTracker = externalMethodTracker,
) {
    init {
        if (bidiPolicy != null && options.iterationLimit != null) {
            // Proposed private class logger; no per-method/per-run guard store.
            migrationLogger.warn {
                "--iteration-limit is ignored by the bidirectional engine; " +
                "the bidirectional field-limit schedule is used"
            }
        }
    }
    // Existing JIRBidiAnalysis dispatch and configured policy remain unchanged.
}
```

Clearing the effective value also prevents a cap from leaking into main's
shared legacy prescan runner. Main's legacy JVM and Go paths still receive
their requested cap. All other options are copied unchanged. Do not use cap
zero as run-0, truncate the bidi schedule or recreate the driver per limit.

Test the original diagnostic and the effective inherited options separately.
Emit once per analyzer construction; repeated form/entry lookup cannot emit
another diagnostic. Verify that `TestProjectAnalyzer` still selects the real
new core when `--ifds-bidirectional` is present. Its existing runner fix needs
verification, not an unnecessary rewrite.

## 10. Native tests and historical fixtures

Use existing suites where they own the behavior. The CSV lists every current
direct public-action/removed-position test consumer, including shared Go tests.
No blanket replacement of every old Position with AnyAfter is permitted.

| Test seam | Required change and assertions |
| --- | --- |
| `JIRRuleFormsTest`, `JIRRuleValidationTest`, `JIRBoundaryFormsTest`, `JIRFormsContractTest` | Use Exact/AnyAfter fixtures; check explicit reach, rejected pass input/RemoveAll/class shapes, complete validation and no partial static operation |
| `JIRCleanerMappingTest`, `JIRLoweredCleanerEffectTest`, `JIRCallTransferTest` | Remove the old String companion expectation; test exact/below selected cleans and direct at-and-below source resets independently; retain field temporary/reversal/layer/H assertions |
| `JIRCallPlanTest`, `JIRCachedPassMethodTest`, `JIRMethodCacheTest`, `JIRRuleViewCacheTest` | Test empty/false/invalid/present-but-no-output fallback cases, original ordinals and warm/cold plan identity |
| `HistoricalJIRCallPlanBuilder` | Adapt only the public types and selected reach/fallback/reset seams; keep it an independent reference for cache tests, not a delegate to the production builder |
| `RuleSpecializationEqualityTest` | Construct wrapped actions; keep label-insensitive semantic equality/hash and meaningful Exact/AnyAfter distinctions |
| `CleanerNormalisationTest`, new `MainMigrationRuleBindingTest` | Check first-marker binding, per-action assumptions, no root assumption for below cleaning, original labels and ignored sink end-action positions |
| Spring forms/acceptance/predefined suites | Check explicit controller stars, conditional exit applicability and unchanged complete cleanup/no-body behavior |
| New `BidiIterationLimitOptionTest` | Check caps absent/0/1/large in both modes, one diagnostic, effective cap null only in bidi and run-1/run-2 limit 1 |
| Existing `RuleTestEngineSelectionTest` | Re-run the actual runner; verify real IterationDriver events rather than only an options flag |

Some root tests already use removed report APIs. Update their test adapters,
not the production reporting contract. The CSV explicitly lists the six
identified root consumers and related helper/acceptance files.

```kotlin
// Test-only observation through existing state while a completed actor is live.
normalFindings = report.entries.map { it.descriptor.key }
targets = completedActors.flatMap { it.targets } // NORMAL IDs or anonymous DEMAND
sinkSeeds = completedActors.flatMap { it.sinkSeeds }

// Resolve PredicateSink.occurrence through the existing frozen form while leased;
// Seed.Sink already has its rule ID. Keep only owned scalar snapshots afterward.
// Use these to test per-rule refinement guidance, not a fictional provisional report.
```

Do not reconstruct DEMAND rule identity from an anonymous DemandTarget alone.
Do not replace a rule-specific assertion by “some demand exists.” Use the
existing sink seeds/occurrence and form observations; use existing processed
edge snapshots for literal geometry. Construct Report.Entry from current
ReportId/ReportDescriptor and test normal root output separately. Do not add
ReportState/SinkWitness back into production or add a new sink observer API.

An old malformed `Position(...AnyField...field)` fixture becomes a serialized
binding test for the selected first-marker rule. Preserve the other rejection
tests. Old selected AT_AND_BELOW reach tests move to the existing generated
reset/core primitive test path; do not delete that coverage when `reach` leaves
the public action API.

## 11. Proofs and implementation correspondence

The [specification proof map](../../spec/main-migration-proofs.md) supplies 51
constructive component theorems. The [implementation proof supplement](../../spec/lean/proposals/main-migration-implementation-20261109/README.md)
imports that exact model and adds 19 implementation-seam theorems:

| Implementation obligation | Supplemental laws |
| --- | --- |
| I01–I06: prepare before selecting fallback; keep original ordinals | `prepared_nonempty_suppresses_fallback`, `prepared_empty_uses_defaults`, false/invalid-row controls and `filtering_keeps_original_ordinals` |
| I07–I08: reject whole rule before output | `rejected_rule_emits_no_partial_vector`, `accepted_rule_preserves_the_complete_vector` |
| I09–I11: canonical per-action cleaner assumptions | `cleaner_assumption_preserves_truth_when_applicable`, `any_cleaner_assumption_is_not_a_root_assumption`, `assumptions_keep_AND_structure` |
| I12–I14: cap isolation and unchanged schedule | `cap_cannot_leak_to_bidi_prescan`, `legacy_cap_passes_through`, `cap_change_does_not_change_bidi_schedule` |
| I15–I16: primitive reset scope and original source IDs | `selected_cleaner_and_source_reset_use_distinct_existing_primitives`, `source_actions_keep_value_region_and_original_ids` |
| I17–I19: finite counterexample controls | Below-only mark versus root mark, unrelated-mark condition retention and ordinal gaps |

These are **70 checked component theorems in total**, including 14 named
finite example proofs. They are not 70 native tests or a universal no-FN or
convergence theorem. The assumption proof requires the assumed literal to
hold; it does not prove all native cleaner approximations from first principles.
Reuse the existing primitive proofs at their stated scopes and retain their
native correspondence gates.

Run the supplemental checker from the repository root:

```bash
python3 spec/lean/proposals/main-migration-implementation-20261109/check.py \
  --output-directory /tmp/main-migration-implementation-proof-review
```

It compiles the pinned specification model, then Plan.lean, then an axiom
audit of all declared laws. It rejects proof holes, custom axioms and classical
choice, pins this proposal and CSV, and records native/convergence proof flags
as false. Use a fresh output directory.

Required native bridges are wrapper/position decoding, complete rule
validation, preservation of identities/hash behavior, exact selected primitive,
actual provider/compiler output, effective cap isolation, actual model/IR
loading, and current report/Target behavior. A passing Lean model or Kotlin
compile alone does not discharge those bridges.

## 12. TDD and implementation steps

| Step | Work | Gate before proceeding |
| --- | --- | --- |
| S0 | Preserve current source/evidence pins, compare main and rebase in the primary checkout | Retain the declared main and branch contracts at conflicts; inventory every changed path |
| S1 | Add failing wrapper/binding/clean/reset fixtures; adapt public types and branch cleaner normalization | Focused configuration, compiler and JVM forms tests pass without a primitive/engine change |
| S2 | Add failing array/fallback tests; remove implicit array arms and select prepared pass rules | Plain/explicit array controls, static-false/invalid/no-output fallback and stable ordinal tests pass |
| S3 | Add Spring and option isolation controls; reconcile provider/prescan hooks | Controller F2F exits, predefined cleanup, original alias view and ignored cap controls pass |
| S4 | Update existing test fixtures and stale test-only report observations | Native suites compile and pass; no old API restored and no assertion silently removed |
| S5 | Validate main model resources, source runner and actual rules suite | Correct model classes/callbacks, real Java bidi events and analyzer/result gates recorded |
| S6 | Run configured OWASP/selected-project validation and report | Reached/completed runs, findings and workload evidence are compared and classified |

Commit coherent, tested steps after the rebase. A conflict/type-error fix is
not permission to alter core admission, field handling or reporting. If a
required main rule binds to a retained unsupported shape, show the bound rule
and request a scope decision before changing the validator/transfer policy.

## 13. Post-implementation experiments

Use the local Gradle validation procedures. Do not use a CLI-pinned old
binary, downloaded CI analyzer/autobuilder artifacts, or a different core.
Record the final source commit, logical runtime classpath, rules/model revision,
FULL mode, alias/static settings and effective field schedule.

1. Run native common/JVM and query/compiler/model tests. Run root tests in the
   intended mode after their current API adapters compile. Record actual XML
   counts; no permanent test exclusions or expected-result relaxations.
2. Run the Java rules suite with `--ifds-bidirectional` and verify actual
   IterationDriver events. Keep Go on its existing engine. Require successful
   analyzer status as well as the result JSON gate. The two known convergence
   failures from the prior runner validation are reference evidence, not a
   waiver or a reason to add an unselected cap/stop rule.
3. Run OWASP and the configured Stirling-PDF, Conductor and Thingsboard campaign
   through Gradle, with the same authorized memory/time/settings. Reuse the
   existing old baseline evidence; do not rerun that baseline.
4. Report finding identities/locations, NORMAL root reports, outgoing demand
   and Targets, latest reached and completed run, engine/barrier times and
   timeout/OOM status. Compare changed inputs separately from adapter behavior.
5. If findings change, trace the exact bound rule/model relation, admitted
   initial, selected primitive, summary and Target path. Classify the cause as
   works-as-on-main input semantics or a works-as-on-bidir regression. A total
   count or main's changed OWASP threshold alone is insufficient evidence.
   Attribution to main is not a quality waiver: report a required flow lost
   by new input rules/models too.
6. For performance changes, capture the current profiling/memory evidence at
   the configured points. Inspect explicit/implicit rule leaf counts, cleaner
   steps, selected getter rules, model CFG/callback reachability and retained
   prescan state. Report observations; do not add another optimization in this
   migration. A speedup is not promised by the proof model.

Use `docs/reports/bidirectional-main-migration-validation.md` and its JSON
data file for the final evidence. Their exact paths are included in the CSV.
Archive or clean old raw captures according to the current procedure while
preserving decoded evidence and source pins.

The adapter lookup complexity remains the existing one: one wrapper dispatch
plus concrete-path interning per position, one predicate DAG build, one linear
prepared-rule selection per call-plan build and existing cached form replay.
There is no new per-input cache or cross-method demand lookup. The migration
does not claim a measured factor improvement or solve known driver cycles.

## 14. Completion and remaining limits

The proposal has no new semantic decision beyond the selected specification.
The implementation supplement checks the additional atomicity, preparation,
normalization and option seams. Native implementation correspondence, actual
rule/model coverage and project convergence are still acceptance work.

Before landing, reconcile the complete inventory with the actual patch. Keep
both classifications for files with both responsibilities. Report unexpected
runtime edits, rejected required rule shapes and failed native/project gates
explicitly; do not hide them behind a successful build or a single finding count.

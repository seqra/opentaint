# Semgrep Rule Diff Design

Status: proposed

Primary implementation area: `core/opentaint-java-querylang`

## 1. Summary

The rule diff tool fully loads an old and a new rule through the existing Semgrep rule pipeline, matches their compiled pattern variants by automata semantics, and only then computes the human-facing structural diff.

The result answers two different questions:

1. Did the declared rule structure change? Examples include an added source, a removed sanitizer, a changed `requires`, a join operand change, or a tag expansion change.
2. Did the compiled matching behavior change? Examples include newly accepted call traces, removed cleaner traces, a changed metavar binding, or a change in the generated `TaintAutomataEdges` state/check behavior.

The ordering is intentional:

```text
full load old and new
        |
        v
extract compiled pattern artifacts
        |
        v
synchronously compare candidate automata pairs
        |
        v
solve a global old-pattern <-> new-pattern matching
        |
        v
lift that matching back to taint/join declarations
        |
        v
render structure changes and bounded trace witnesses
```

List positions, state IDs, join aliases, and formula-manager predicate IDs are not used as cross-version identity.

## 2. Goals and non-goals

### Goals

- Run the complete normal loader pipeline on both sides, including rule references, tags, overrides, language rewriting, register-automata construction, `TaintAutomataEdges` generation, and final taint-rule emission.
- Preserve the intermediate artifacts needed for comparison without changing the generated runtime rules.
- Match pattern-operation combinations before computing structural changes.
- Use each captured `TaintAutomataEdges.automata` as the complete graph for synchronous simulation.
- Compare automata semantically rather than by Kotlin data-class equality or graph isomorphism.
- Respect metavar binding/register behavior, accept versus dead/cleaner termination, global-state checks, and generated-edge behavior.
- Produce a deterministic, bounded sample of old-only, new-only, and compiled-output-divergence traces.
- Distinguish `equivalent`, `changed`, `inconclusive`, and `load failed`.
- Support normal matching rules, taint rules, join rules, referenced library rules, tag-expanded joins, and overrides.
- Provide a reusable Kotlin API, deterministic JSON, a human-readable renderer, and a CLI entry point.

### Non-goals for the first implementation

- Reconstructing a source-code example that compiles and executes a trace. A symbolic, replayable method-event trace is sufficient.
- Attributing every compiled edge to one individual `pattern`, `pattern-not`, or `pattern-inside`. Intersections, complements, minimization, and formula simplification merge those origins. Version 1 attributes a difference to a compiled pattern-operation combination and its declared rule part.
- Treating textual YAML differences, comments, anchors, or formatting as semantic changes.
- Using final serialized taint rules to reconstruct automata. The required information has already been discarded at that point.
- Declaring equivalence when the solver times out or encounters an unsupported guard theory.

## 3. Existing pipeline and design constraints

### 3.1 Current load stages

The relevant pipeline is:

```text
Semgrep YAML
  -> Formula
  -> NNF/DNF RawSemgrepRule variants
  -> parsed language patterns
  -> language rewrites
  -> SemgrepPatternActionList
  -> SemgrepRuleAutomata
  -> TaintRegisterStateAutomata
  -> role/join preparation
  -> TaintAutomataEdges
  -> TaintRuleFromSemgrep
```

The current implementation is split across:

- `SemgrepYamlParsing.kt`: YAML models, formula parsing, taint parts, joins, and NNF/DNF conversion.
- `SemgrepRuleAutomataBuilder.kt`: parse, rewrite, action-list, automata, and duplicate-removal stages.
- `TaintRegisterAutomataCreation.kt`: conversion to register-state automata.
- `TaintRuleProcessing.kt` and `JoinRuleProcessing.kt`: role- and join-specific preparation.
- `TaintAutomataGeneration.kt` and `TaintEdgesGeneration.kt`: cleaned register automata and final edge projection.
- `SemgrepRuleLoader.kt`: orchestration and final `TaintRuleFromSemgrep` production.

`SemgrepRuleLoader.RuleLoadResult` currently exposes only generated rules, metadata, and disabled IDs. The built automata are private loader state, and `TaintAutomataEdges` instances exist only as locals during final conversion.

### 3.2 Provenance is lost before the final edge stage

A formula is normalized to DNF and may be fanned out again by a language rewrite. `RuleWithMetaVars` currently carries only the compiled value and resolved metavariable information. As a result, a final automaton cannot be reliably mapped back to:

- the declared source/sink/propagator/sanitizer;
- the DNF alternative produced from that declaration; or
- the rewrite alternative produced by the language strategy.

Duplicate removal can also merge semantically equal variants. The loader must preserve a set of origins when it performs that merge.

### 3.3 `TaintAutomataEdges.edges` is not a complete automaton

`TaintAutomataEdges` embeds a cleaned `TaintRegisterStateAutomata`, but its three edge lists are a sparse projection used to generate runtime rules:

- `edges` contains selected intermediate register/global-state transitions;
- `edgesToFinalAccept` contains emitted sink transitions;
- `edgesToFinalDead` contains emitted cleaner transitions.

Transitions that do not change a register or participate in global-state propagation can be absent from those lists. Therefore, iterating only `TaintAutomataEdges.edges` cannot prove trace-language equivalence.

The synchronous simulation must run over `TaintAutomataEdges.automata.successors`. The three emitted lists, `checkGlobalState`, `globalStateAssignStates`, and `metaVarInfo` are compared as observable outputs attached to the full transitions.

### 3.4 Taint roles specialize a pattern before edge generation

Sources, sinks, propagators, and sanitizers seed different initial/accept variables and may add or fork states before `TaintAutomataEdges` is built. The captured comparison unit is therefore the exact, role-specialized `TaintAutomataEdges` produced by the full load. Its embedded `.automata` is the graph used for pattern matching and synchronous simulation.

A pattern moved between roles can consequently be a divergent rather than an exactly equivalent candidate. The global matcher may pair such candidates using proved similarity and shortest divergence as a cost, but must label the mapping as edited/heuristic rather than semantically equivalent.

### 3.5 Generated identifiers are not semantic identity

- `State.id` values depend on traversal and cleanup order.
- register values are assignment-epoch state IDs and must be renamed with the state correspondence.
- `MethodFormulaManager` predicate IDs are allocated independently on the two sides.
- tag-expanded join item IDs such as `alias#0` depend on expansion order.
- generated mark names contain rule, part, and state-derived prefixes.

Comparison uses structural `Predicate` values and def-use relationships, with alpha-renaming for internal state, epoch, and generated-mark identifiers.

## 4. Public behavior

### 4.1 Inputs

Each side is a `RuleInput`:

```kotlin
data class RuleInput(
    val rulesRoot: Path,
    val selectedRuleId: String?,
    val inputFiles: List<Path>? = null,
)
```

Directory input uses the directory as `rulesRoot`. File input uses the file's parent as `rulesRoot` and its basename as the registered relative path. Explicit input files must normalize to descendants of the root; they are deduplicated and sorted.

The root is loaded as a complete rule universe so the selected rule can resolve:

- referenced library rules;
- inline child normal/taint rules declared by a join;
- tag selections;
- cross-file overrides.

A fresh `SemgrepRuleLoader` is created for each side because the loader owns mutable registration, parsed-rule, built-rule, and disabled-rule state.

Join-to-join references remain unsupported and produce the existing blocking load diagnostic.

If `selectedRuleId` is absent, selection succeeds only when exactly one enabled, non-library top-level rule is available. Input paths are sorted before registration.

### 4.2 Result states

```kotlin
enum class RuleDiffStatus {
    EQUIVALENT,
    CHANGED,
    INCONCLUSIVE,
    LOAD_FAILED,
}
```

- `EQUIVALENT`: full loads succeeded and no declared or compiled semantic difference was found.
- `CHANGED`: full loads succeeded and at least one structure or automata difference was proved.
- `INCONCLUSIVE`: loading succeeded, no change was proved, and an equivalence question exceeded a limit or used unsupported semantics. Partial comparisons may still be included.
- `LOAD_FAILED`: at least one selected rule did not complete the full load.

Status aggregation is `LOAD_FAILED` first. Otherwise, any proved semantic or declared difference produces `CHANGED`, even if other candidate comparisons were inconclusive; the result then has `comparisonComplete = false`. `INCONCLUSIVE` is used only when no difference was proved and equivalence could not be completed. Thus exit code `2` always means at least one proved change, while exit code `1` includes an unresolved no-change result.

An absent rule is not interpreted as a removed rule when the corresponding side has a blocking load error.

### 4.3 Diagnostics

Both sides are always loaded, even if the first fails. The result contains normalized `SemgrepLoadTrace` entries with:

- side;
- file and rule ID;
- load step;
- stable diagnostic code/type;
- category and blocking severity;
- message.

A selected rule fails to load when it is absent, has a blocking diagnostic in its dependency closure, or has no final emitted artifact. The detailed loader records ref, tag-expansion, and override dependency edges so ownership can be computed. File-level YAML failure always fails that side because dependency attribution cannot be recovered from an unparsed file; this is a deliberate conservative exception. Blocking errors in unrelated parsed rules are warnings by default and failures under `strictLoad`.

Unsupported selected languages receive an explicit diagnostic instead of appearing as a generic missing rule. This requires moving unsupported-language reporting ahead of the current supported-rule partition. Diagnostic DTOs gain a stable code derived from the message type; comparing newly introduced/resolved diagnostics uses that code plus normalized context, while rendered exception text remains display-only.

## 5. Detailed load artifact

### 5.1 Backward-compatible loader API

Keep `loadRules(...)` unchanged as a projection. Add a detailed entry point:

```kotlin
data class DetailedRuleLoadResult(
    val runtime: SemgrepRuleLoader.RuleLoadResult,
    val artifacts: Map<String, LoadedRuleArtifact>,
    val diagnostics: List<RuleLoadDiagnostic>,
)

fun SemgrepRuleLoader.loadRulesDetailed(
    severity: List<Severity> = emptyList(),
    ruleIdFilter: List<String> = emptyList(),
    ruleIdExclude: List<String> = emptyList(),
): DetailedRuleLoadResult
```

Both public methods call one private load implementation with an optional artifact collector. Normal `loadRules` passes no collector; `loadRulesDetailed` passes one and returns its artifacts. Automata must not be regenerated in a second pass, because that can duplicate diagnostics and drift from the artifacts that actually emitted the runtime rule.

### 5.2 Provenance

```kotlin
enum class RulePartKind {
    MATCH, SOURCE, SINK, PROPAGATOR, SANITIZER,
}

data class RulePartOrigin(
    val ownerRuleLocalId: String,
    val kind: RulePartKind,
    val declarationIndex: Int,
)

data class RuleVariantOrigin(
    val part: RulePartOrigin,
    val dnfIndex: Int,
    val rewriteIndex: Int,
)
```

Origins are stable only within one load. They are for grouping and display, never cross-version identity.

The automata builder attaches the part origin before NNF/DNF conversion, adds the DNF ordinal during raw-rule expansion, and adds the rewrite ordinal after `strategy.rewriter.rewrite`. `map` and `flatMap` operations preserve it through action-list, automata, and register-automata conversion.

Do not make provenance accidentally change semantic duplicate removal. Variants equal under the existing action-list plus resolved-metavariable dedup key are merged and retain the union of their origins. Compiled-variant multiplicity is therefore collapsed exactly as it is today; declared-part multiplicity remains represented by the origin set and declared structure.

Exact YAML line and column information is not currently available in the parsed model. Adding source spans is a separate parser enhancement.

### 5.3 Artifact model

```kotlin
data class LoadedRuleArtifact(
    val descriptor: LoadedRuleDescriptor,
    val declared: DeclaredRuleStructure,
    val resolved: ResolvedRuleStructure,
    val compiledVariants: List<LoadedCompiledVariant>,
    val uses: List<LoadedPatternUse>,
    val emittedRule: TaintRuleFromSemgrep<*>,
)

data class LoadedCompiledVariant(
    val localId: String,
    val origins: Set<RuleVariantOrigin>,
    val displayByOrigin: Map<RuleVariantOrigin, PatternDisplaySnapshot>,
    val resolvedMetaVars: ResolvedMetaVarInfo,
)

data class LoadedPatternUse(
    val localId: String,
    val compiledVariantId: String,
    val context: PatternContext,
    val effectiveEdges: TaintAutomataEdges,
    val generationSemantics: GenerationSemantics,
    val emittedGroupIds: List<String>,
)
```

`PatternDisplaySnapshot` contains normalized raw positive, negative, inside, and not-inside strings plus modifiers. It is captured before language rewriting, keyed by origin, and is explanatory only; it does not drive semantic matching.

The split is one-to-many: one deduplicated compiled variant can be used by several taint marks, join branches, or tag-expanded operands. A `LoadedPatternUse` is the unit passed to the candidate matcher because it owns the exact `TaintAutomataEdges`; origins and display stay on the shared compiled variant.

`GenerationSemantics` records the use-level information not contained in `TaintAutomataEdges`, including source/sink requirements and labels, propagator mark policy, sanitizer clean/by-side-effect policy, and join endpoint/composition policy. It is compared as structure/context, not folded into the `TaintAutomataEdges` language-equivalence claim.

`PatternContext` records data required to interpret the fully loaded variant:

```kotlin
sealed interface PatternContext {
    data class Normal(val part: RulePartOrigin) : PatternContext
    data class JoinOperand(
        val branchLocalId: String,
        val itemLocalId: String,
        val resolvedRuleId: String,
        val side: JoinSide,
        val joinMetaVar: MetavarAtom,
        val underlyingPart: RulePartOrigin,
    ) : PatternContext
}
```

### 5.4 Declared and resolved structures

The artifact keeps both views because each can change independently.

`DeclaredRuleStructure` contains:

- matching versus taint versus join mode;
- taint declarations and modifiers (`exact`, `control`, `by-side-effect`, `label`, `requires`, `from`, `to`);
- declared join refs, rule/tag selector, alias, renames, and `on` expressions;
- relevant rule options and metadata.

`ResolvedRuleStructure` contains:

- effective taint variants grouped by declared origin;
- resolved override targets;
- resolved join items and target rule IDs;
- tag expansion results;
- parsed join operations and endpoints;
- final join branches and operand sides.

Declared part count and loaded variant count are separate. For example, one source containing `pattern-either` is one declared source but can produce several DNF/rewrite variants.

### 5.5 Capturing the exact effective edges

Refactor conversion into two conceptual steps:

```text
materialize generation contexts and diff artifacts
                    |
                    v
emit language-specific runtime rules from those contexts
```

For normal taint rules, the capture point is after `prepareTaintRules`, `generateTaintAutomataEdges`, and the role-specific edge reclassification currently performed in `generateEdgeCtx`. For joins it is after the left/right initial and final variables have affected edge generation. Join composition policies applied later are captured separately in `GenerationSemantics`.

An unscoped callback inside `generateTaintAutomataEdges` is insufficient: at that point it cannot reliably distinguish a source from a sink or a left from a right join operand, and it may observe edges before role-specific reclassification.

No second graph or loader sidecar is required. The normalizer reads the complete graph directly from:

```text
effectiveEdges.automata.successors
```

It builds a derived observation index from `edges`, `edgesToFinalAccept`, and `edgesToFinalDead`, keyed by source, destination, and edge kind and then partitioned by normalized guard/effect when more than one emitted edge shares that key. `globalStateAssignStates` and `metaVarInfo` are component observations. Ambiguous association that cannot be resolved symbolically returns `Inconclusive` rather than requiring mutation of the existing automata types.

The embedded automaton's raw accept/dead state bits and the emitted categories are distinct. For example, role reclassification can move accept edges into ordinary edges or cleaner edges without rewriting the embedded final-state sets. Names such as `AcceptOutput` and `CleanerOutput` refer to emitted-list categories, not necessarily the raw destination state's terminal bit.

## 6. Overall comparison algorithm

```kotlin
class RuleDiffEngine {
    fun compare(
        old: LoadedRuleArtifact,
        new: LoadedRuleArtifact,
        options: RuleDiffOptions = RuleDiffOptions(),
    ): RuleDiffResult
}
```

The phases are:

1. Validate language compatibility and artifact invariants.
2. Normalize each pattern use without using state IDs or collection iteration order.
3. Compare plausible old/new `effectiveEdges.automata` pairs and populate a candidate matrix.
4. Solve a deterministic, global minimum-cost maximum bipartite matching.
5. Infer declared-part and join-item mapping from the matched uses and their origin sets.
6. Compute structural differences using those mappings.
7. Render bounded trace samples and deterministic structure changes.

Structural positions, list indices, aliases, and roles do not establish identity or primary match cost. Semantically necessary exported-variable roles can constrain a comparison; structural placement is otherwise used only after automata comparison as a deterministic display tie-break, and ambiguity is reported.

## 7. Automata normalization

### 7.1 Normalized transition system

Normalize each effective variant as a symbolic transducer:

```kotlin
data class NormalizedAutomaton(
    val initial: StateKey,
    val terminals: Map<StateKey, TerminalBits>,
    val outgoing: Map<StateKey, List<NormalizedTransition>>,
    val metaVars: MetaVarUniverse,
)

data class NormalizedTransition(
    val ref: FullTransitionRef,
    val kind: EventKind,
    val guard: NormalizedGuard,
    val effects: Set<BindingAssignment>,
    val destination: StateKey,
    val output: NormalizedOutput,
)
```

Collect states from the initial state, terminal sets, successor keys, and every successor destination. As an artifact invariant, validate that non-synthetic register epochs resolve to unambiguous states and reject state-ID clashes. Initial seeded epochs and transformed/forked states are handled explicitly rather than assumed to have a graph-state origin.

All map/set/list inputs are sorted for canonical formatting and hashing. Predicate conjunctions are unordered and idempotent.

### 7.2 Two-sorted guards

`IsMetavar` is not an ordinary method predicate. In generated semantics it is a binding/mark membership check, while positive occurrences in effects assign the current event position to a variable.

Use:

```kotlin
data class NormalizedGuard(
    val method: MethodGuard,
    val bindings: BindingFormula,
)

data class BindingToken(
    val variable: CanonicalMetaVar,
    val assignmentEpoch: EpochKey,
)

data class BindingAssignment(
    val token: BindingToken,
    val position: Position,
)
```

`MethodGuard` contains signature, type, constant, arity, annotation, and modifier constraints. `BindingFormula` contains position-to-register-token membership/equality atoms derived using the source state's register.

Existing method-formula SAT machinery is reused only for `MethodGuard`. Binding constraints are solved with the current metavariable and assignment-epoch correspondence. A satisfiable event must satisfy both theories.

### 7.3 Metavariable policy

Version 1 uses strict user-metavariable names:

```kotlin
enum class MetaVarCompareMode {
    STRICT_NAMES,
}
```

State IDs, assignment epochs, and generated internal marks are always alpha-renamed because they are loader artifacts. User-written metavariable names are retained as semantic names in v1, including basic/complex atoms, method/type/string metavariables, focus variables, and join endpoints. A local `$X` to `$Y` rename is therefore reported as a change.

A later `ALPHA_EQUIVALENT_LOCALS` mode can map non-exported local basic metavariables with structurally identical constraints. Complex variables, exported/focus/join variables, regex/formula constraint equivalence, and unsupported meta-to-meta constraint operations require a separately specified extension; v1 must not silently accept them.

## 8. Synchronous simulation

### 8.1 Result type

```kotlin
sealed interface AutomataCompareResult {
    data class Equivalent(
        val relation: StateRelation,
        val stats: AutomataCompareStats,
    ) : AutomataCompareResult

    data class Different(
        val oldOnly: List<TraceWitness>,
        val newOnly: List<TraceWitness>,
        val outputChanges: List<TraceOutputDelta>,
        val partialRelation: StateRelation,
        val stats: AutomataCompareStats,
    ) : AutomataCompareResult

    data class Inconclusive(
        val reason: InconclusiveReason,
        val partial: PartialAutomataComparison,
    ) : AutomataCompareResult
}
```

Accept and dead are separate terminal observations. A trace ending in accept on one side and dead on the other is a proved difference.

### 8.2 Deterministic fast path

First use SAT to verify that same-kind outgoing guards are pairwise disjoint at every reachable state. Do not assume determinism merely because upstream automata were determinized: formula expansion and register rewrites no longer retain a trustworthy determinism flag.

For verified deterministic automata, breadth-first search the symbolic product:

```text
ProductConfiguration =
  (old state or bottom,
   new state or bottom,
   assignment-epoch bijection)
```

At each configuration:

1. Compare the old and new `{accept, dead}` terminal bits.
2. For each event kind, SAT-check every old/new guard overlap.
3. For each satisfiable overlap, align read tokens and assignments, extend the epoch mapping, compare emitted outputs, and enqueue the destination pair.
4. Check old guard coverage not covered by the union of new guards, and symmetrically new guard coverage not covered by old guards.
5. On a coverage gap, first compare the taken transition's emitted output with implicit `Silent` on the missing side. Then transition the missing side to a rejecting bottom state. Continue until a raw terminal or emitted-output difference is observed; a missing silent transition alone is not necessarily a language difference.

Conceptual pseudocode:

```text
queue <- initial product configuration

while queue is not empty:
    current <- remove first

    if terminalBits(old) != terminalBits(new):
        record shortest terminal witness

    for each event kind:
        oldOut <- outgoing(old, kind)
        newOut <- outgoing(new, kind)

        for oldEdge in oldOut:
            for newEdge in newOut:
                region <- SAT_REGION(oldEdge.guard AND newEdge.guard)
                if region is satisfiable:
                    mapping <- align bindings/effects(current, oldEdge, newEdge, region)
                    if mapping fails:
                        record binding/output witness
                    else:
                        compare emitted observations
                        enqueue destinations with parent and region

        for oldEdge in oldOut:
            region <- SAT_REGION(oldEdge.guard AND NOT OR(newOut.guards))
            if region is satisfiable:
                compare oldEdge.output with Silent
                enqueue(oldEdge.to, bottom)

        repeat coverage check in the other direction
```

`AnalysisEnd`, if present in the embedded automaton, is a discrete event without a method guard.

Existing `methodFormulaSat` returns only a Boolean. V1 therefore defines `SAT_REGION` as `Sat(canonicalSatisfiableRegion)`, `Unsat`, or `Unknown`: it may retain a simplified satisfiable cube/formula rather than a concrete input model. Concrete model extraction is an optional later solver extension.

The breadth-first parent map produces a shortest symbolic distinguishing trace under the fixed strict-metavariable policy and explored solver semantics. Stable sorting of event kinds, normalized guards, and destinations makes witness selection deterministic. If any search limit is reached, minimality and equivalence are not claimed.

### 8.3 Emitted-edge comparison as transducer output

Language equivalence can relate one state on one side to several equivalent states on the other. Therefore, do not require graph isomorphism or an emitted-edge multiset bijection.

Every full transition is decorated, using the observation index derived from the same `TaintAutomataEdges`, with:

- `Silent`, `IntermediateOutput`, `AcceptOutput`, or `CleanerOutput`;
- effective cleaned edge guard and effect;
- `checkGlobalState`;
- whether the destination assigns global state.

The product compares those decorations for each satisfiable input partition, up to state/epoch/generated-mark alpha-renaming. Component-level `metaVarInfo` is compared structurally after canonical ordering; unsupported semantic constraint equivalence returns inconclusive.

If the accepted/cleaned trace language is equal but an output decoration differs, report `COMPILED_EDGE_CHANGE`. This can change generated runtime rules or precision even though the core pattern language is unchanged.

### 8.4 Nondeterminism

Version 1 detects reachable overlapping same-kind guards and returns `INCONCLUSIVE(UNSUPPORTED_NONDETERMINISTIC_REGISTER_AUTOMATON)`. Pairwise bisimulation is not an acceptable equivalence proof for nondeterministic automata.

A later exact fallback may use symbolic subset construction with finite equality partitions for live registers. Because this is an output-labelled system, it must retain the correlation between each emitted output and its destination/run, for example by grouping post-configurations by normalized output. Comparing only an output set and a union post-set is not exact. This extension is outside the v1 completion criteria.

### 8.5 Solver failures and limits

Options include:

```kotlin
data class AutomataCompareLimits(
    val deadline: Duration,
    val maxProductConfigurations: Int,
    val maxSatCalls: Int,
)
```

Timeout, state/minterm explosion, unsupported type/metavar constraint intersection, or solver exceptions return `Inconclusive`; they never return `Equivalent`.

Cache SAT queries by canonical formula digest and cache component comparisons by normalized artifact pair plus comparison options.

### 8.6 Complexity

For verified deterministic automata the product has at most approximately `|Qold| * |Qnew| * Cmapping` configurations. Per configuration and event kind, overlap work is `outOld * outNew` plus coverage checks. Space is proportional to visited product configurations and parent records.

A future nondeterministic subset construction can reach `2^(|Qold| + |Qnew|)` state subsets, with up to `2^b` guard minterms and an additional equality-partition factor for live registers. V1 avoids this cost by returning inconclusive.

## 9. Trace witnesses

```kotlin
enum class TraceDirection { OLD_ONLY, NEW_ONLY }
enum class TraceObservation { ACCEPT, DEAD, BINDING, COMPILED_OUTPUT }

data class TraceWitness(
    val direction: TraceDirection,
    val observation: TraceObservation,
    val steps: List<TraceStep>,
)

data class TraceStep(
    val event: EventKind,
    val satisfiableRegion: SymbolicGuardRegion,
    val oldTransition: TransitionDisplay?,
    val newTransition: TransitionDisplay?,
    val bindingsBefore: BindingSnapshot,
    val bindingsAfter: BindingSnapshot,
)
```

The satisfiable region retains a canonical guard conjunction and binding equality classes. If a future solver supplies a concrete model, the renderer may additionally show concrete method/class/name/arity/position values.

Every witness is replayed against both normalized automata before it is returned. The report calls them samples, not an exhaustive enumeration.

V1 returns one shortest witness per direction and observation category. More samples require bounded k-shortest search or multiple parent records per product configuration; that is an explicit later extension rather than an assumption about ordinary visited-set BFS. Include truncation and search statistics in the result.

## 10. Pattern matching before structural diff

### 10.1 Pairwise candidate matrix

Flatten each rule to loaded pattern uses. Compare all language-compatible pairs using `effectiveEdges.automata`, with caching. Structural positions do not determine candidates.

Each candidate receives a proof category and cost:

1. effective `TaintAutomataEdges` equivalent: cost 0;
2. proved divergent but similar: finite edit cost based on a longer common trace prefix, divergence kind, and canonical event/register features;
3. incomparable/inconclusive: forbidden as a certain match and retained only as an unresolved explanation;
4. dummy candidate: explicit added or removed use.

Similarity is only an assignment heuristic. It never turns a divergent or inconclusive comparison into equivalence.

### 10.2 Global assignment

Solve an unmatched-allowed minimum-cost bipartite assignment across old and new uses. Do not greedily match by role, list position, pattern text, or first equal candidate.

The implementation may use a Hungarian/min-cost-flow solver; expected complexity is `O(max(m,n)^3)` after pair comparisons. Dedicated dummy rows and columns represent additions and removals. A divergent real pair is selected only when its edit cost is lower than `remove(old) + add(new)`; inconclusive pairs have forbidden/infinite cost for certain mapping.

If several zero-cost assignments exist because several uses share an equivalent deduplicated compiled variant, choose a deterministic display mapping and add an `ambiguousMappings` record. Compiled duplicates remain collapsed as today; declared multiplicity is preserved through origins and declared-part matching.

### 10.3 Declared part mapping

After use matching, follow `compiledVariantId` and group origins by `RulePartOrigin`. Infer old/new declared-part mapping from the number and quality of matched uses, again using deterministic global assignment.

This lets the report distinguish:

- one added source declaration;
- an added DNF alternative inside an existing source;
- a language rewrite that now emits an additional variant;
- an edited source candidate paired to a sanitizer after effective-automata comparison.

## 11. Structural diff

### 11.1 Common rule-level changes

Report separately from automata behavior:

- matching/taint/join mode change;
- short declared rule ID, message, severity, and selected metadata change;
- path-qualified rule ID/location change, reported separately so moving a file does not look like a declared ID edit;
- language or primitive-tracking option change;
- override target change;
- declared versus loaded variant counts;
- load diagnostics newly introduced or resolved.

Metadata changes do not imply a trace-language change.

### 11.2 Taint rules

Using mapped declared parts, report:

- sources, sinks, propagators, and sanitizers added or removed;
- a mapped pattern moved between roles;
- modifier changes: `exact`, `control`, `by-side-effect`, label, and `requires`;
- propagator `from`/`to` changes;
- focus/metavariable-constraint changes;
- declaration count versus expanded-variant count changes;
- effective compiled-edge changes for each mapped part.

List reordering alone is ignored because matching is semantic and multiplicity-aware.

Some parsed modifiers are not currently consumed by all downstream generation paths. The report labels these as declaration-only changes when the effective automata/output comparison remains equivalent.

### 11.3 Join rules

Preserve and compare both declared and resolved topology.

Declared changes include:

- ref added/removed;
- `rule` versus `tag` selector change;
- alias and rename change;
- join operator or endpoint metavariable change;
- `on` condition added/removed.

Resolved changes include:

- tag expansion member added/removed;
- override target change;
- referenced operand behavior change;
- left/right operand move;
- join branch added/removed;
- join operation endpoints changed after item mapping.

Join items are mapped by their contained automata and resolved semantics before aliases or `alias#index` IDs are compared. Operations are then rewritten through that item mapping and compared as normalized endpoint tuples.

## 12. Report model

```kotlin
@Serializable
data class RuleDiffResult(
    val schemaVersion: Int,
    val status: RuleDiffStatus,
    val comparisonComplete: Boolean,
    val hasProvenChanges: Boolean,
    val old: RuleDescriptorDto,
    val new: RuleDescriptorDto,
    val diagnostics: List<RuleLoadDiagnosticDto>,
    val patternMatches: List<PatternMatchDto>,
    val unmatchedPatterns: List<UnmatchedPatternDto>,
    val ambiguousMappings: List<AmbiguousMappingDto>,
    val structure: StructureDiffDto?,
    val traceSamples: List<TraceDeltaDto>,
    val limits: DiffLimitSummaryDto,
)
```

Serialize report DTOs, not internal automata or solver objects. Every list is deterministically sorted by semantic path, change kind, canonical pattern digest, and witness key.

Suggested human output:

```text
CHANGED  old/path.yaml:rule -> new/path.yaml:rule

Structure
  source[old:0] -> sanitizer[new:1]
    role changed: source -> sanitizer
    declared by-side-effect: null -> true
  join operand payments-api
    resolved target added: lib/new-handler.yaml:new-handler

Compiled behavior
  sink[old:1] -> sink[new:0]
    removed accepting trace (1 sample, shortest length 2)
      CALL com.example.Input.read()  bind $X=result
      CALL com.example.Db.exec(arg0=$X)

  source[old:0] -> sanitizer[new:1]
    edited automata candidate; emitted role behavior changed
```

## 13. Service and CLI

### 13.1 Kotlin facade

Place the reusable loader artifact, comparison engine, DTOs, and renderers under:

```text
core/opentaint-java-querylang/src/main/kotlin/
  org/opentaint/semgrep/pattern/diff/
```

The shared package must not import `GoLanguageStrategy`; `opentaint-go-querylang` already depends on `opentaint-java-querylang`.

Put a concrete Java+Go facade/runner in root `core`, which depends on both query-language modules:

```kotlin
class RuleDiffService {
    fun compare(
        old: RuleInput,
        new: RuleInput,
        strategies: List<LanguageStrategy<*, *>>,
        options: RuleDiffOptions,
    ): RuleDiffRunResult
}
```

### 13.2 CLI contract

Proposed command:

```text
opentaint rules diff OLD NEW
  [--old-rule-id ID]
  [--new-rule-id ID]
  [--language java|go]
  [--format text|json]
  [--output PATH]
  [--no-traces]
  [--strict-load]
```

`--language` restricts the installed strategy list to exactly one language and validates the selected rule. Without it, the resolved language is recorded on each descriptor; cross-language rules are rejected as incomparable before automata comparison.

For the JVM-first implementation, add `RuleDiffRunner` and a dedicated `JavaExec` `runRuleDiff` Gradle task. Invoke its fully qualified class from the analyzer fat jar with `java -cp analyzer.jar org.opentaint...RuleDiffRunner`; the existing jar manifest names a different main class.

For a later Go CLI wrapper, prefer a JVM `--output` JSON file and let Go read/render it. The current Java subprocess runner routes process output through logging, so direct stdout pass-through must not be assumed.

Stdout contains only the selected report format. Operational diagnostics go to stderr.

Exit codes follow the repository's existing domain-result convention:

- `0`: equivalent;
- `2`: at least one change was proved, including a changed result with `comparisonComplete = false`;
- `1`: invalid input, load failed, incomparable/inconclusive, or internal failure.

## 14. Determinism requirements

- Sort rule files before registration.
- Sort selected rule candidates and resolved tag members.
- Canonically sort predicates, metavariables, transitions, terminals, and constraints.
- Never expose hash-map/set iteration order.
- Use BFS and stable outgoing-transition order for shortest witnesses.
- Use stable tie-breaking in bipartite matching and report ambiguity.
- Do not use the DOT/view printer as report output or golden-test input; its graph traversal and labels are visualization-oriented.

## 15. Implementation plan

### Phase 0: characterization tests

Before refactoring, capture current behavior for:

- normal matching and taint rules;
- source/sink/propagator/sanitizer expansion;
- joins, tag expansion, and overrides;
- diagnostics and disabled rules;
- final `TaintRuleFromSemgrep` output.

Acceptance: the later detailed-load refactor produces byte-for-byte/equality-equivalent runtime results and the same diagnostics when artifact capture is not requested.

### Phase 1: provenance and detailed loading

1. Add part/DNF/rewrite origins.
2. Propagate owner-qualified origin sets and per-origin display snapshots through `RuleWithMetaVars` transformations in Java and Go rewrite paths.
3. Change duplicate removal to merge origins without changing semantic deduplication.
4. Snapshot declared override edges before `resolveRuleOverrides`, then capture effective targets, join refs, tag expansions, and dependency edges during resolution.
5. Introduce declared and resolved structure snapshots plus `GenerationSemantics`.
6. Refactor normal, taint, and join conversion to expose each pattern use and capture the exact effective `TaintAutomataEdges` without regenerating it.
7. Add production traversal and stable codes for `SemgrepLoadTrace` diagnostics, including unsupported-language registration.
8. Add `loadRulesDetailed`; retain `loadRules` through the same internal path with a nullable collector.

Suggested files:

```text
pattern/diff/LoadedRuleArtifact.kt
pattern/diff/RuleProvenance.kt
pattern/diff/RuleLoadDiagnostic.kt

Modified pipeline files include SemgrepRuleLoader.kt,
SemgrepYamlParsing.kt, SemgrepRuleAutomataBuilder.kt,
RuleWithMetaVars call sites in JavaLanguageStrategy.kt and GoRuleRewriter.kt,
TaintRegisterAutomataCreation.kt, TaintRuleProcessing.kt,
JoinRuleProcessing.kt, and RuleConversionCtx.kt.
```

Acceptance: every compiled variant has an explicit one-to-many mapping to its pattern uses and emitted groups; every use owns the exact `TaintAutomataEdges` used by generation; joins retain declared and resolved views; existing loader results and diagnostics remain unchanged for normal loading.

### Phase 2: canonical automata model and guard solver

1. Implement invariant validation and full-state collection.
2. Canonicalize predicates, constraints, metavariables, registers, and output observations.
3. Split method guards from binding guards/effects.
4. Import both sides' structural predicates into a common formula manager.
5. Add `SAT_REGION` by re-interning structural predicates and rebuilding conjunction/negated-union formulas in a common manager; return a canonical satisfiable region or typed unknown, with caching and deadlines.
6. Implement strict user-metavariable comparison and alpha-renaming only for internal state/epoch/generated identifiers.
7. Implement reachability and outgoing-guard determinism validation.

Suggested files:

```text
pattern/diff/automata/AutomataNormalizer.kt
pattern/diff/automata/GuardSolver.kt
pattern/diff/automata/MetaVarMatcher.kt
pattern/diff/automata/NormalizedAutomaton.kt
```

Acceptance: state/predicate ID renumbering and collection reordering normalize identically; binding read/write differences remain distinguishable.

### Phase 3: synchronous equivalence and witnesses

1. Implement deterministic symbolic product BFS.
2. Compare terminal bits and transition output observations.
3. Implement bottom-state coverage handling.
4. Store parent/region records and render one shortest witness per direction/category.
5. Add symbolic-region replay validation.
6. Detect reachable nondeterminism and return the typed v1 inconclusive result.
7. Return typed inconclusive results for every proof limit or unsupported solver operation.

Suggested files:

```text
pattern/diff/automata/SynchronousAutomataDiff.kt
pattern/diff/automata/TraceWitness.kt
pattern/diff/automata/TraceReplay.kt
```

Acceptance: equivalent is returned only by an exhausted exact product; every reported witness replays with different observations on the two sides.

### Phase 4: component matching and structural diff

1. Build and cache the candidate-pair matrix.
2. Define equivalence, edited-candidate, add/remove, forbidden, and unresolved candidate costs.
3. Implement unmatched-allowed min-cost bipartite use matching with dedicated dummies.
4. Detect ambiguous duplicate mappings.
5. Infer declared-part and resolved join-item mappings.
6. Implement common, taint, and join structural differencing.
7. Keep declaration-only and compiled-behavior changes separate.

Suggested files:

```text
pattern/diff/PatternMatcher.kt
pattern/diff/PartMatcher.kt
pattern/diff/StructureDiffer.kt
pattern/diff/JoinStructureDiffer.kt
pattern/diff/RuleDiffEngine.kt
```

Acceptance: reordered patterns are unchanged, declared duplicates preserve multiplicity through origins, and join/taint changes are attributed through automata mappings rather than indices.

### Phase 5: DTOs, renderers, and JVM runner

1. Define versioned serializable report DTOs.
2. Add deterministic JSON and text renderers. Either add the `kotlinx-serialization-json` runtime dependency to `opentaint-java-querylang` or keep JSON rendering in root `core`; do not rely on the serialization compiler plugin alone.
3. Add `RuleDiffService` and `RuleDiffRunner` in root `core` with Java and Go strategies.
4. Add CLI parsing, selectors, limits, formats, output file, and exit codes.
5. Add fat-jar invocation smoke tests.

Suggested files:

```text
pattern/diff/report/RuleDiffDto.kt
pattern/diff/report/RuleDiffJsonRenderer.kt
pattern/diff/report/RuleDiffTextRenderer.kt
core/src/main/kotlin/.../RuleDiffRunner.kt
```

Acceptance: text and JSON are stable across repeated runs; stdout/stderr and exit codes follow the contract.

### Phase 6: Go CLI integration and performance hardening

1. Add `opentaint rules diff` as a thin wrapper around the JVM runner.
2. Read the JSON output file and render or pass it through.
3. Add cache hit/miss and solver/product statistics.
4. Establish production defaults from a representative rules corpus.
5. Add cancellation coverage and memory-bound stress tests.
6. Optionally add bounded k-shortest multi-sample witnesses and a `--max-traces` option.

## 16. Test plan

### 16.1 Loader and provenance

- One declaration, one variant.
- `pattern-either`/DNF produces several variants grouped under one declaration.
- Language rewrite fan-out retains rewrite ordinals.
- Duplicate compiled variants merge origin sets and do not duplicate runtime rules.
- Source, sink, propagator, and sanitizer artifacts capture the exact effective edges.
- Join left/right operands capture context and declared/resolved topology.
- Tag expansion and override dependency closure.
- Malformed YAML, duplicate IDs, disabled rule, unsupported language, and final conversion failure.
- Unrelated broken rule under strict and non-strict loading.
- Java and Go detailed loads.

### 16.2 Automata equivalence

- State IDs, predicate IDs, and insertion order differ only: equivalent.
- Same language represented with a split guard versus a union guard: equivalent.
- Extra equivalent state versus minimized state: equivalent.
- Old guard broader or narrower: shortest directional witness.
- Accept versus dead on the same event sequence: terminal difference.
- `$X` assigned then reused versus a distinct `$Y`: binding difference.
- Assignment position changes from result to argument: effect difference.
- Local consistent `$X` to `$Y` rename: changed under the v1 strict-metavariable policy.
- Same full trace language but global-state/output observation toggled: compiled-edge change.
- Loop and missing-transition/bottom behavior.
- Overlapping reachable guards return the typed v1 nondeterminism inconclusive result.
- Low product-state/SAT/deadline limits: inconclusive, never equivalent.
- Unsupported metavar/type intersection: inconclusive.

### 16.3 Matching and structure

- Taint parts reordered only: no change.
- Identical duplicate parts: multiplicity preserved and ambiguity reported.
- Source/sink/propagator/sanitizer added and removed.
- A source-to-sanitizer move whose effective automata diverge is either paired as an edited candidate or reported as remove/add; it is never called equivalent.
- Modifier, label, requirement, focus, and propagator endpoint changes.
- One declared source gains an alternative: variant-count change, not added declaration.
- Matching to taint or taint to join mode change.
- Join ref/selector/alias/rename/operator/metavariable changes.
- Tag-expanded join member added or removed.
- Join operand reorder only: no false removal/addition.
- Test explicitly proves automata matching precedes structural attribution.

### 16.4 Reports and integration

- Golden JSON with a fixed schema version.
- Golden human text for equivalent, changed, inconclusive, and load-failed cases.
- Trace suppression and product-search truncation summary.
- Repeat the same diff many times and assert identical bytes.
- File/root selectors and ambiguous selector errors.
- Exit codes `0`, `2`, and `1`.
- Stdout contains report only; diagnostics use stderr.
- Analyzer fat-jar classpath invocation.
- Go wrapper command construction and exit propagation.
- Auto-selection when all other top-level rules are failed, library, or disabled.
- File move/rename between roots, distinguishing path-qualified location from short declared ID.

### 16.5 Verification commands

At the relevant phases run:

```bash
cd core
./gradlew :opentaint-java-querylang:test :opentaint-go-querylang:test
./gradlew test :projectAnalyzerJar

cd ../cli
go test ./...
```

## 17. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Formula/register equivalence is expensive | Deterministic fast path, SAT and pair caches, explicit limits, exact inconclusive result |
| Provenance changes duplicate semantics | Merge origin sets using the old semantic duplicate key |
| Sparse emitted edge lists are mistaken for a DFA | Always simulate the embedded full automaton and treat emitted edges as outputs |
| Role specialization makes an exact move non-equivalent | Let automata comparison establish divergence; use bounded edited-candidate cost for attribution and never label it equivalent |
| Equivalent automata have different graph shapes | Product language/transducer equivalence, not state bijection or graph isomorphism |
| Nondeterminism produces a false proof | V1 returns inconclusive; never use pairwise bisimulation as proof |
| SAT/type operations are incomplete | Catch unsupported/TODO/timeout as typed inconclusive |
| Duplicate patterns make mapping arbitrary | Global matching, deterministic tie-break, and explicit ambiguity |
| Tag alias indices shift | Match resolved items by automata/target semantics, not `alias#index` |
| Load failure looks like removal | Require successful full artifacts before semantic comparison |
| Hash collection order changes output | Canonical normalization and stable sorting at every boundary |

## 18. Completion criteria

The tool is complete when:

1. Both sides use fresh loaders and complete final runtime-rule generation.
2. Every selected rule has declared/resolved structure, compiled-variant origins, one-to-many pattern uses, exact `TaintAutomataEdges`, generation-semantics, dependency, and diagnostic artifacts.
3. Automata equivalence ignores generated IDs but preserves register binding and emitted-edge semantics.
4. Structural mapping is derived from completed automata comparisons, not list position or pattern text.
5. Every proved divergence can include a replay-validated symbolic trace sample.
6. Solver/complexity limits produce `INCONCLUSIVE`, never a false `EQUIVALENT`.
7. Taint and join structure changes are deterministic and preserve declared multiplicity despite compiled deduplication.
8. Existing loader outputs and diagnostics remain compatible.
9. JSON/text output is stable across repeated runs and covered by golden tests.

## 19. Repository evidence

Key implementation anchors used by this design:

- Public loader result and orchestration: `SemgrepRuleLoader.kt:112-153`.
- Parsed normal/join/override model: `SemgrepRuleLoader.kt:193-213`.
- Normal automata build checkpoint: `SemgrepRuleLoader.kt:287-315`.
- Join resolution and tag-expanded item construction: `SemgrepRuleLoader.kt:401-465`.
- Formula and taint-part parsing: `SemgrepYamlParsing.kt:317-328, 420-446`.
- NNF/DNF raw variant conversion: `SemgrepYamlParsing.kt:463-580`.
- Action-list and automata pipeline: `SemgrepRuleAutomataBuilder.kt:50-145`.
- Generic rule shape and taint part modifiers: `SemgrepRule.kt:1-85`.
- Register/state/edge model: `TaintRegisterStateAutomata.kt:9-64`.
- Register automata creation: `TaintRegisterAutomataCreation.kt:34-48`.
- Role specialization and edge materialization: `TaintRuleProcessing.kt:37-75, 145-213, 225-320`.
- Join operand conversion: `JoinRuleProcessing.kt:31-100, 156-255`.
- Full cleanup and edge-generation entry point: `TaintAutomataGeneration.kt:38-46`.
- Sparse emitted-edge selection and terminal split: `TaintEdgesGeneration.kt:32-171`.
- `TaintAutomataEdges` representation: `TaintAutomataEdges.kt:5-36`.
- Predicate allocation and structural predicate lookup: `MethodFormulaManager.kt:8-31`.
- Existing method-formula SAT: `MethodFormulaSimplifier.kt:69-86`.
- Existing automata visualization printer: `conversion/automata/Printer.kt:97-145`.

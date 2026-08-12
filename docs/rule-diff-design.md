# Semgrep Rule Diff Design

Status: service and CLI implemented; SAT-region guard comparison remains follow-up work

Primary implementation area: `core/opentaint-java-querylang`

## 1. Summary

The rule diff tool compares two rules in three ordered stages:

```text
full-load both rule universes
            |
            v
extract structure and DNF cubes at NormalRule<Formula>
            |
            v
match exact cubes across rule parts
            |
            v
compile and compare automata only for remaining cubes
            |
            v
lift the cube mapping back to structural and trace diffs
```

The central choices are:

1. Structural input is the parsed `NormalRule<Formula>`, not final emitted rules. Structural changes are computed by lifting the completed cube mapping back to this model.
2. Every formula is normalized to DNF using the same normalization used by `convertToRawRule`.
3. Exactly equal cubes are matched structurally and require no automata comparison.
4. Only non-matched cubes are lazily compiled through the existing action-list, automata, register-automata, and `TaintAutomataEdges` pipeline.
5. Synchronous simulation uses `TaintAutomataEdges.automata` as the complete graph.
6. The current rule-conversion pipeline is not instrumented or modified for diff capture. The diff utility is a separate consumer of loader snapshots and existing conversion functions.
7. User-written metavariable names are semantic. `$X` and `$Y` are different and are never alpha-equated.

The tool reports both declaration-level changes and proved behavioral trace changes. A structural change can have no automata-language change, and an automata divergence is always attached to the unmatched cubes that caused it.

## 2. Goals and non-goals

### Goals

- Fully load both sides before computing a semantic diff.
- Resolve the same rule universe as normal loading, including library refs, tag refs, inline join children, and overrides.
- Extract taint/matching structure from parsed formulas and taint-part metadata, then compute its diff from cube mappings.
- Compare join declarations and their resolved normal/taint operands.
- Use DNF cubes as the first pattern-to-pattern mapping layer.
- Avoid building a second set of automata for cubes already matched exactly.
- Compare unmatched `TaintAutomataEdges` by synchronous simulation of their embedded automata.
- Produce deterministic samples of new and removed traces.
- Preserve current loader and converter behavior when the diff feature is unused.
- Return explicit `equivalent`, `changed`, `inconclusive`, and `load failed` outcomes.

### Non-goals for v1

- Injecting collectors, callbacks, provenance, or diff types into `SemgrepRuleAutomataBuilder`, `RuleConversionCtx`, `TaintRuleProcessing`, `JoinRuleProcessing`, or final rule emission.
- Comparing YAML formatting, comments, anchors, or list spelling when the parsed structure is the same.
- Treating different user metavariable names as equivalent.
- Proving equivalence for reachable nondeterministic register automata. V1 returns `INCONCLUSIVE` for that case.
- Generating compilable source-code examples from traces. A replayable symbolic method-event trace is sufficient.
- Recursively loading join rules as operands of another join; current loading rejects join-to-join refs.

## 3. Existing pipeline

The current normal-rule pipeline is:

```text
Semgrep YAML
  -> SemgrepRule<Formula>
  -> NNF/DNF
  -> RuleWithMetaVars<RawSemgrepRule, RawMetaVarInfo>
  -> parsed language patterns
  -> language rewrites
  -> SemgrepPatternActionList
  -> SemgrepRuleAutomata
  -> TaintRegisterStateAutomata
  -> role-specific state preparation
  -> TaintAutomataEdges
  -> TaintRuleFromSemgrep
```

Relevant code:

- `SemgrepYamlParsing.kt` parses formulas, taint parts, joins, and implements NNF/DNF conversion.
- `SemgrepRuleAutomataBuilder.kt` performs raw conversion, language parsing, metavariable resolution, rewriting, action-list conversion, and automata construction.
- `TaintRegisterAutomataCreation.kt` creates register-state automata.
- `TaintRuleProcessing.kt` prepares source/sink/propagator/sanitizer state variables.
- `TaintAutomataGeneration.kt` produces `TaintAutomataEdges`.
- `SemgrepRuleLoader.kt` owns parsing, reference resolution, full building, and final emission.

The existing public `RuleLoadResult` exposes only emitted rules, metadata, and disabled IDs. The parsed `NormalRule<Formula>` and `JoinRule<Formula>` are private loader state. The design adds read-only loader extension points for those snapshots; it does not capture objects from inside conversion.

## 4. Full loading and loader extension points

### 4.1 Full-load contract

Each side uses a fresh `SemgrepRuleLoader` because a loader owns mutable registered, parsed, built, override, and disabled-rule state.

The service:

1. discovers and sorts all input YAML files;
2. registers the complete old rule universe in an old loader;
3. registers the complete new rule universe in a new loader;
4. calls the existing full `loadRules` pipeline on both;
5. collects load diagnostics and parsed/resolved snapshots;
6. selects one top-level rule on each side;
7. starts diffing only if both selected rules fully loaded.

Full loading remains authoritative for support and validity. A parsed snapshot without a corresponding successfully emitted rule is not diffable.

Directory input uses the directory as `rulesRoot`. File input uses the file's parent as `rulesRoot` and its basename as the registered relative path. Explicit files must normalize to descendants of the root; paths are deduplicated and sorted.

### 4.2 Read-only extension API

Add a loader-level extension interface:

```kotlin
interface SemgrepRuleLoaderExtension {
    fun onNormalRuleParsed(rule: ParsedNormalRuleSnapshot) {}
    fun onJoinRuleParsed(rule: ParsedJoinRuleSnapshot) {}
    fun onOverrideResolved(override: ResolvedOverrideSnapshot) {}
    fun onJoinRuleResolved(rule: ResolvedJoinRuleSnapshot) {}
}
```

The loader accepts an optional list of extensions:

```kotlin
class SemgrepRuleLoader(
    strategies: List<LanguageStrategy<*, *>>,
    extensions: List<SemgrepRuleLoaderExtension> = emptyList(),
)
```

These callbacks are invoked only from `SemgrepRuleLoader` orchestration:

- after a `NormalRule<Formula>` has been parsed and accepted;
- after a declared join has been parsed;
- after override resolution determines its effective target;
- after join refs/tags have been resolved into effective item targets.

No callback is added to action-list conversion, automata building, taint preparation, edge generation, or final rule generation. Normal loading with no extensions follows the current control flow and creates no diff artifacts.

### 4.3 Snapshot types

```kotlin
data class ParsedRuleDescriptor(
    val qualifiedRuleId: String,
    val shortRuleId: String,
    val language: String?,
    val relativePath: Path,
    val isLibraryRule: Boolean,
    val isDisabled: Boolean,
)

data class ParsedNormalRuleSnapshot(
    val descriptor: ParsedRuleDescriptor,
    val rule: SemgrepRule<Formula>,
    val primitiveTracking: Boolean,
    val overrideTarget: String?,
    val metadata: RuleMetadata,
)

data class ParsedJoinRuleSnapshot(
    val descriptor: ParsedRuleDescriptor,
    val refs: List<SemgrepYamlJoinRuleRef>,
    val operations: List<SemgrepJoinRuleOn>,
)

data class ResolvedJoinRuleSnapshot(
    val descriptor: ParsedRuleDescriptor,
    val items: Map<String, ResolvedJoinItemSnapshot>,
    val operations: List<TaintAutomataJoinOperation>,
)
```

Snapshots copy immutable parsed/resolved values and do not expose mutable loader maps. The extension collector also records dependency edges from refs, tag expansion, inline children, and overrides so blocking diagnostics can be attributed to the selected rule's dependency closure.

### 4.4 Diagnostics

Both sides finish loading even if one fails. The diff result contains diagnostics with side, file, rule ID, step, category, blocking severity, stable message type/code, and display text.

The selected rule is `LOAD_FAILED` when:

- it is absent or unsupported;
- it has a blocking diagnostic;
- a rule in its resolved dependency closure has a blocking diagnostic;
- it has no final emitted rule despite having a parsed snapshot.

An unparsed file-level YAML error conservatively fails that side because dependency ownership is unknowable. Blocking failures in unrelated parsed rules are warnings unless `strictLoad` is enabled.

Unsupported languages must be diagnosed before the current supported-rule partition silently removes them.

## 5. Structural model

### 5.1 Rule structure

Structural diff works on the snapshot's parsed model:

```kotlin
sealed interface StructuralRule {
    data class Matching(
        val part: StructuralPart,
    ) : StructuralRule

    data class Taint(
        val sources: List<StructuralTaintSource>,
        val sinks: List<StructuralTaintSink>,
        val propagators: List<StructuralTaintPropagator>,
        val sanitizers: List<StructuralTaintSanitizer>,
    ) : StructuralRule

    data class Join(
        val declared: ParsedJoinRuleSnapshot,
        val resolved: ResolvedJoinRuleSnapshot,
    ) : StructuralRule
}
```

Each normal-rule part contains its original modifiers and a DNF cube multiset.

### 5.2 DNF cube extraction

Use exactly the formula normalization semantics behind `convertToRawRule`.

Add an additive parsing helper without changing the existing conversion call path:

```kotlin
data class FormulaDnfCube(
    val ordinal: Int,
    val formula: Formula,
    val raw: RuleWithMetaVars<RawSemgrepRule, RawMetaVarInfo>,
    val key: CanonicalCubeKey,
)

fun formulaToDnfCubes(
    formula: Formula,
    trace: SemgrepRuleLoadStepTrace,
): List<FormulaDnfCube>
```

Implementation:

1. reuse the existing `normalizeToNNF(...).toDNF()` implementation;
2. preserve each resulting cube as a single conjunction `Formula` for later lazy compilation;
3. feed that cube through the existing `convertToRawRule` conversion to obtain `RawSemgrepRule` and `RawMetaVarInfo`;
4. require exactly one raw result for a DNF cube;
5. create a deterministic canonical key.

The existing `convertToRawRule(rule, trace)` behavior and callers remain unchanged.

### 5.3 Canonical cube key

`CanonicalCubeKey` contains:

- sorted positive pattern strings;
- sorted `pattern-not` strings;
- sorted `pattern-inside` strings;
- sorted `pattern-not-inside` strings;
- sorted focus metavariable names;
- canonical metavariable constraint formulas.

Order within a conjunction is ignored. Multiplicity is retained. Alternatives remain separate cubes.

Metavariable names are not renamed or normalized away. A cube using `$X` has a different key from the same text using `$Y`. This strict policy also applies later during automata comparison.

### 5.4 Taint-part structure

The following fields are retained at the `NormalRule<Formula>` layer and require no converter instrumentation:

- source: `exact`, `control`, `bySideEffect`, `label`, and `requires`;
- sink: `requires`;
- propagator: `from`, `to`, and `bySideEffect`;
- sanitizer: `exact` and `bySideEffect`;
- focus metavariables and raw metavariable constraints;
- declared part count and DNF cube count.

Declaration count and cube count are separate. One source containing `pattern-either` is one declared source with several cubes, not several declared sources.

### 5.5 Exact cube matching

Flatten the old and new `NormalRule<Formula>` structures into `ContextualCube` multisets. Match equal `CanonicalCubeKey` values globally across normal-rule parts; do not restrict matching to source-to-source or sink-to-sink. This permits an identical cube moved from source to sanitizer to establish its own identity before the role change is reported.

Duplicate exact cubes cancel one-for-one. When several exact assignments exist, prefer the same rule-part kind and equal modifiers only as deterministic tie-breakers, and report the mapping ambiguity. List positions are never identity.

The output of this phase is:

```kotlin
data class CubeDiffPlan(
    val exactCubeMatches: List<CubeMatch>,
    val unmatchedOldCubes: List<ContextualCube>,
    val unmatchedNewCubes: List<ContextualCube>,
)
```

Only the two unmatched lists proceed to automata compilation. Exact matches plus later automata matches form the complete cube mapping. The structural differ then lifts that mapping back to declarations and compares role, modifiers, declaration counts, cube counts, and mode.

Declarations containing no successfully extracted cubes are matched separately by strict modifier/context keys with explicit add/remove dummies. A successfully full-loaded rule should rarely require this fallback, but it keeps structure accounting total.

## 6. Join structural diff

Join diff also starts with structure, not automata.

### 6.1 Declared join changes

Compare:

- ref added/removed;
- `rule` versus `tag` selector;
- selector value;
- alias;
- metavar renames;
- `on` operator;
- left/right alias and metavar endpoint;
- declared inline child rule changes.

### 6.2 Resolved join changes

Compare:

- resolved target rule IDs;
- tag expansion member additions/removals;
- effective override targets;
- resolved operation endpoints;
- left/right operand membership;
- branches created by tag expansion.

Aliases and tag-generated item IDs are not sufficient identity. First match declared refs by selector/target overlap, then rewrite resolved operations through that ref mapping.

For every resolved operand whose effective target exists on both sides, diff its `ParsedNormalRuleSnapshot` using the same DNF process as a top-level normal rule. Exact operand cubes are cancelled structurally; only changed operand cubes are compiled.

Join-to-join references remain a load failure under current loader semantics.

## 7. Lazy compilation of unmatched cubes

### 7.1 Important distinction

The required full load has already compiled the selected rule in the normal loader pipeline. However, that pipeline does not retain a cube-to-automaton map. The diff utility performs its own per-cube compilation only for structurally unmatched cubes.

It does not recompile exact matched cubes.

### 7.2 Cube context

```kotlin
sealed interface CubeContext {
    data object Matching : CubeContext
    data class Source(val declaration: SemgrepTaintSource<Formula>) : CubeContext
    data class Sink(val declaration: SemgrepTaintSink<Formula>) : CubeContext
    data class Propagator(val declaration: SemgrepTaintPropagator<Formula>) : CubeContext
    data class Sanitizer(val declaration: SemgrepTaintSanitizer<Formula>) : CubeContext
    data class JoinOperand(
        val side: JoinSide,
        val joinMetaVar: MetavarAtom,
        val underlying: CubeContext,
    ) : CubeContext
}

data class ContextualCube(
    val ownerRuleId: String,
    val declarationKind: RulePartKind,
    val declarationOrdinal: Int,
    val cube: FormulaDnfCube,
    val context: CubeContext,
)
```

### 7.3 Separate cube compiler

Implement the compiler in the diff package:

```kotlin
class RuleCubeCompiler(
    private val strategy: LanguageStrategy<*, *>,
) {
    fun compile(
        cube: ContextualCube,
        ruleContext: ParsedNormalRuleSnapshot,
        trace: SemgrepRuleLoadTrace,
    ): CompiledCube
}

data class CompiledCube(
    val source: ContextualCube,
    val variants: List<TaintAutomataEdges>,
)
```

The compiler is not called by `SemgrepRuleLoader` or the normal converter.

It composes existing pipeline operations:

1. wrap the single cube `Formula` in the original matching/taint part and preserve its modifiers;
2. call `SemgrepRuleAutomataBuilder.build` for that single-cube rule;
3. call `createTaintAutomata` on the result;
4. apply existing role preparation helpers from `TaintRuleProcessing` for the selected part;
5. call `generateTaintAutomataEdges` for each rewritten/built variant;
6. return the resulting list without emitting `TaintRuleFromSemgrep`.

No conversion function receives a diff collector or diff-specific branch.

### 7.4 Role preparation

The cube compiler must reproduce the inputs that affect `TaintAutomataEdges`:

- matching: empty initial and accept variable sets;
- source: source focus/accept variables and whether `requires` needs an initial taint-check variable;
- sink: focus variables or the generated sink requirement variable;
- propagator: declared `from` as initial and `to` as accept;
- sanitizer: the generated cleaner position at initial and accept;
- join left/right: the join metavar as the relevant accept or initial variable.

Reuse `prepareTaintSourceRules`, `prepareTaintNonSourceRules`, and `generateTaintAutomataEdges` rather than copying these algorithms. If a required helper is currently private, make it `internal` without changing its implementation or its normal callers.

Source labels and requirements used to prepare a non-source part are derived from the full `ParsedNormalRuleSnapshot`, so isolated compilation observes the same rule context.

Role-specific final runtime composition policies are already compared structurally (`requires`, labels, propagator endpoints, sanitizer flags, and join endpoints). The automata phase compares the `TaintAutomataEdges` returned by `generateTaintAutomataEdges`; it does not claim to diff the final serialized taint-rule objects.

### 7.5 Cache

Cache compilation by:

```text
(language, canonical cube key, cube context, relevant rule-level label context)
```

The cache is per diff run. Failures are cached as typed inconclusive results with their diagnostics.

## 8. Pairing non-matched cubes

After both unmatched sides are compiled, create a candidate matrix.

Candidate categories:

1. `AUTOMATA_EQUIVALENT`: all compiled variants can be matched equivalently; cost 0.
2. `AUTOMATA_DIFFERENT`: a divergence is proved; finite edit cost based on structural similarity and common trace prefix.
3. `INCONCLUSIVE`: compilation, SAT, or determinism prevented proof; forbidden as a certain match.
4. `ADDED`/`REMOVED`: dummy match against the empty automaton set.

Use an unmatched-allowed min-cost bipartite assignment. A divergent old/new pair is selected only when its edit cost is less than remove plus add. Inconclusive pairs may be displayed as possible relationships but cannot establish equivalence or a certain structural mapping.

One cube can produce several compiled variants after language rewriting. Compare those variant lists as multisets with another inner unmatched-allowed assignment. Exact per-variant equivalence cancels a pair; unmatched variants are compared with bottom to produce directional traces. V1 does not merge different rewritten variants into an implicit union automaton.

Combine exact DNF matches and selected automata candidate matches, then infer declaration mapping by maximum mapped-cube overlap. Compare the retained `NormalRule<Formula>` structure through that mapping. Thus automata are built only for non-matched cubes, while the final structural diff is still computed at the parsed normal-rule layer.

For an automata-equivalent pair with different cube keys, report `CUBE_EXPRESSION_CHANGED` with no trace-language delta. For an automata-different selected pair, report the cube expression change plus its directional/generated-edge witnesses. Exact cube pairs contribute identity but no cube-expression change.

## 9. `TaintAutomataEdges` comparison

### 9.1 Comparison object

For each compiled variant, use:

```text
TaintAutomataEdges.automata.initial
TaintAutomataEdges.automata.successors
TaintAutomataEdges.automata.finalAcceptStates
TaintAutomataEdges.automata.finalDeadStates
```

as the complete register automaton.

The separate `edges`, `edgesToFinalAccept`, and `edgesToFinalDead` collections are a sparse generated-edge projection, not the whole graph. They are compared after graph simulation as observable generated-edge categories, together with `checkGlobalState`, `globalStateAssignStates`, and `metaVarInfo`.

### 9.2 Strict metavariable semantics

User metavariable names must match exactly everywhere:

- `MetavarAtom` keys;
- method-name metavariables;
- type metavariables;
- string-value metavariables;
- focus metavariables;
- join endpoints;
- raw and resolved constraint maps.

Only generated state IDs, register assignment-epoch IDs, and internal generated marks are alpha-renamed. A user rename from `$X` to `$Y` is a structural and automata difference.

### 9.3 Normalized events

Normalize every full transition into:

```kotlin
data class NormalizedTransition(
    val kind: EventKind,
    val methodGuard: MethodGuard,
    val bindingGuard: BindingGuard,
    val assignments: Set<BindingAssignment>,
    val destination: StateKey,
    val generatedOutput: GeneratedEdgeObservation,
)
```

`IsMetavar` is interpreted as register binding semantics, not merely as an ordinary predicate:

- reads constrain an event position to the token stored in the source state's register;
- positive effects assign the current event position to the destination register epoch.

Non-metavariable predicates form the symbolic method guard.

All maps, sets, predicates, and constraints are canonically sorted. Formula-manager predicate IDs and state IDs are never compared directly.

### 9.4 Synchronous deterministic product

First use satisfiability checks to verify that reachable same-kind outgoing guards are pairwise disjoint. If not, return the v1 nondeterminism inconclusive result.

For deterministic automata, breadth-first search product configurations:

```text
(old state or bottom,
 new state or bottom,
 assignment-epoch correspondence)
```

At each configuration:

1. compare raw accept/dead terminal bits;
2. group outgoing transitions by method event kind;
3. find satisfiable old/new guard overlaps;
4. enforce exact user-metavariable names and binding reads;
5. align assignments and extend epoch correspondence;
6. compare generated-edge observations;
7. enqueue destination pairs;
8. find old guard regions not covered by new guards and vice versa;
9. compare a coverage transition's generated output with `Silent`, then enqueue the other side against bottom.

Missing transitions alone are not differences until they produce a different terminal or generated observation. Bottom stays bottom while the other side continues.

Conceptual pseudocode:

```text
queue <- (old.initial, new.initial, emptyEpochMap)

while queue is not empty:
    cfg <- queue.removeFirst()

    if terminalBits(cfg.old) != terminalBits(cfg.new):
        record witness

    for kind in EventKind:
        oldOut <- outgoing(cfg.old, kind)
        newOut <- outgoing(cfg.new, kind)

        for oldEdge in oldOut:
            for newEdge in newOut:
                region <- SAT_REGION(oldEdge.guard AND newEdge.guard)
                if region is satisfiable:
                    nextEpochMap <- alignBindingsAndEffects(cfg, oldEdge, newEdge)
                    if alignment fails:
                        record binding witness
                    else if outputs differ:
                        record generated-edge witness
                    else:
                        enqueue(oldEdge.to, newEdge.to, nextEpochMap)

        for oldEdge in oldOut:
            region <- SAT_REGION(oldEdge.guard AND NOT OR(newOut.guards))
            if region is satisfiable:
                compare oldEdge.output with Silent
                enqueue(oldEdge.to, bottom, cfg.epochMap)

        repeat coverage in the other direction
```

### 9.5 SAT interface

Existing `methodFormulaSat` returns only a Boolean. The diff wrapper exposes:

```kotlin
sealed interface SatRegionResult {
    data class Sat(val region: CanonicalGuardRegion) : SatRegionResult
    data object Unsat : SatRegionResult
    data class Unknown(val reason: String) : SatRegionResult
}
```

It re-interns structural `Predicate` objects from both sides into one `MethodFormulaManager`, builds overlap/coverage formulas, and retains a canonical satisfiable cube or guard region for witness display. It does not require a concrete method model.

Timeouts, unsupported type/metavariable constraint operations, and solver exceptions return `Unknown` and make the comparison inconclusive unless another path has already proved a difference.

### 9.6 Generated-edge projection

For a full transition, derive applicable generated observations from the same `TaintAutomataEdges` using source state, destination state, event kind, and normalized guard/effect. Categories are:

- `Silent`;
- ordinary generated edge;
- edge in `edgesToFinalAccept`;
- edge in `edgesToFinalDead`.

Also compare `checkGlobalState`, destination global-state assignment, and component `metaVarInfo`.

The embedded automaton's raw accept/dead bits are distinct from generated-edge categories. Role processing can reclassify generated edge lists without rewriting raw final-state sets.

If multiple generated edges cannot be associated with a full transition unambiguously, compare their normalized observation sets over the current satisfiable guard region. If correlation remains ambiguous, return `INCONCLUSIVE` rather than requiring instrumentation inside edge generation.

### 9.7 Nondeterminism and limits

Reachable overlapping same-kind guards return:

```text
INCONCLUSIVE(UNSUPPORTED_NONDETERMINISTIC_REGISTER_AUTOMATON)
```

V1 never uses pairwise bisimulation as an equivalence proof for nondeterministic automata.

Limits include a total deadline, maximum product configurations, maximum SAT calls, and maximum formula size. Hitting a limit returns inconclusive; it never returns equivalent.

## 10. Trace witnesses

```kotlin
enum class TraceDirection { OLD_ONLY, NEW_ONLY }
enum class TraceObservation { ACCEPT, DEAD, BINDING, GENERATED_EDGE }

data class TraceWitness(
    val direction: TraceDirection,
    val observation: TraceObservation,
    val oldCube: CubeDisplay?,
    val newCube: CubeDisplay?,
    val steps: List<TraceStep>,
)

data class TraceStep(
    val eventKind: EventKind,
    val satisfiableRegion: CanonicalGuardRegion,
    val oldTransition: TransitionDisplay?,
    val newTransition: TransitionDisplay?,
    val bindingsBefore: BindingSnapshot,
    val bindingsAfter: BindingSnapshot,
)
```

Breadth-first parents yield the shortest distinguishing trace under the fixed strict-metavariable policy and explored solver semantics. If a limit is reached, shortestness and equivalence are not claimed.

Every witness is replayed symbolically against both normalized automata before reporting.

V1 returns one witness per direction and observation category. Comparing an added cube with bottom produces a new trace; comparing a removed cube with bottom produces a removed trace. Bounded k-shortest multi-sample support can be added later.

## 11. Diff result

```kotlin
enum class RuleDiffStatus {
    EQUIVALENT,
    CHANGED,
    INCONCLUSIVE,
    LOAD_FAILED,
}

@Serializable
data class RuleDiffResult(
    val schemaVersion: Int,
    val status: RuleDiffStatus,
    val comparisonComplete: Boolean,
    val hasProvenChanges: Boolean,
    val oldRule: RuleDescriptorDto,
    val newRule: RuleDescriptorDto,
    val diagnostics: List<RuleLoadDiagnosticDto>,
    val structureChanges: List<StructureChangeDto>,
    val exactCubeMatches: List<CubeMatchDto>,
    val automataCubeMatches: List<CubeMatchDto>,
    val addedCubes: List<CubeDto>,
    val removedCubes: List<CubeDto>,
    val traceSamples: List<TraceWitnessDto>,
    val inconclusiveComparisons: List<InconclusiveComparisonDto>,
)
```

Status aggregation:

1. a selected-side loading failure gives `LOAD_FAILED`;
2. any proved declaration, cube, or automata difference gives `CHANGED`;
3. if changes are proved but another comparison is unresolved, status remains `CHANGED` and `comparisonComplete` is false;
4. if no difference is proved but equivalence cannot be completed, status is `INCONCLUSIVE`;
5. only a fully completed comparison with no differences is `EQUIVALENT`.

Metadata policy:

- short declared rule ID, message, severity, and selected metadata changes are structural changes;
- path-qualified ID is a location descriptor, so moving a file is not reported as changing the short declared ID;
- metadata-only changes produce `CHANGED` with no trace witnesses.

All DTO lists are sorted deterministically. Internal graphs and solver objects are not serialized.

## 12. Service and CLI

### 12.1 Service

```kotlin
class RuleDiffService(
    strategies: List<LanguageStrategy<*, *>>,
) {
    fun compare(
        old: RuleInput,
        new: RuleInput,
        options: RuleDiffOptions = RuleDiffOptions(),
    ): RuleDiffResult

    fun comparePaths(
        oldPath: Path,
        newPath: Path,
        oldRuleId: String,
        newRuleId: String = oldRuleId,
        options: RuleDiffOptions = RuleDiffOptions(),
    ): RuleDiffResult
}
```

Place structural, cube, automata, and report models under:

```text
core/opentaint-java-querylang/src/main/kotlin/
  org/opentaint/semgrep/pattern/diff/
```

The shared module does not import `GoLanguageStrategy`. Put the concrete Java+Go service facade and runner in root `core`, which depends on both query-language modules.

### 12.2 CLI

```text
./gradlew runRuleDiff --args='OLD NEW
  --old-rule-id ID
  [--new-rule-id ID]
  [--language java|go]
  [--format text|json]
  [--output PATH]
  [--no-traces]'
```

`--language` restricts the strategy list to one language. Without it, record the resolved strategy in each descriptor and reject cross-language comparison before cube compilation.

Exit codes:

- `0`: equivalent;
- `2`: at least one change proved, even if `comparisonComplete` is false;
- `1`: invalid input, load failure, inconclusive-without-proved-change, or internal failure.

Add a fully qualified `RuleDiffRunner` and a dedicated `JavaExec` Gradle task. The existing analyzer jar has another manifest main, so invoke the runner with `java -cp analyzer.jar <fully-qualified-RuleDiffRunner>`.

For later Go CLI integration, prefer JVM JSON output to a file and let Go read/render it; current Java subprocess output is routed through logging.

## 13. Determinism

- Sort input paths before registration.
- Treat declaration and cube collections as multisets.
- Canonically sort pattern lists, constraints, predicates, transitions, and reports.
- Use strict user-metavariable names.
- Never expose hash-map or hash-set iteration order.
- Use stable BFS transition order.
- Use deterministic assignment tie-breaking and report ambiguous equal-cost declaration/cube mappings.
- Do not use DOT/view printer output as golden report text.

## 14. Implementation plan

### Phase 0: characterization

Add tests that snapshot current:

- parsing and `convertToRawRule` output;
- matching and taint full-load output;
- join/tag/override resolution;
- diagnostics and disabled-rule behavior;
- final `TaintRuleFromSemgrep` output.

Acceptance: enabling no loader extensions produces the same outputs and diagnostics.

### Phase 1: loader snapshots and DNF API

1. Add immutable snapshot DTOs and `SemgrepRuleLoaderExtension`.
2. Invoke extensions only from loader parse/resolve orchestration.
3. Record ref/tag/override dependency edges and stable diagnostic codes.
4. Diagnose unsupported selected languages before filtering.
5. Add `formulaToDnfCubes` using existing NNF/DNF implementation without changing `convertToRawRule` callers.
6. Add deterministic `CanonicalCubeKey`.

Suggested files:

```text
pattern/diff/load/RuleDiffLoadCollector.kt
pattern/diff/load/RuleSnapshots.kt
pattern/diff/structure/FormulaDnfCube.kt
pattern/diff/structure/CanonicalCubeKey.kt
```

Modified existing files are limited to `SemgrepRuleLoader.kt`, the additive DNF helper in `SemgrepYamlParsing.kt`, and diagnostic exposure.

Acceptance: snapshots reproduce private loader structure; normal load behavior remains unchanged; a formula's cube list agrees one-for-one with `convertToRawRule`.

### Phase 2: structural extraction and exact cube matching

1. Convert parsed matching/taint parts to structural declarations.
2. Implement strict canonical cube equality.
3. Flatten contextual cubes across rule-part kinds.
4. Cancel exact cubes as multisets with deterministic, ambiguity-aware tie-breaking.
5. Produce `CubeDiffPlan` with only unmatched cubes for compilation.
6. Extract common rule metadata/options for later structural comparison.

Suggested files:

```text
pattern/diff/structure/RuleStructure.kt
pattern/diff/structure/ExactCubeMatcher.kt
```

Acceptance: identical/reordered structures compile zero diff cubes; an exact cube moved across roles also compiles zero cubes; one changed alternative compiles only the old/new changed cubes.

### Phase 3: standalone cube compiler

1. Implement single-cube rule wrapping for each `CubeContext`.
2. Reuse `SemgrepRuleAutomataBuilder.build` and `createTaintAutomata`.
3. Reuse role preparation and `generateTaintAutomataEdges` outside normal conversion.
4. Change only necessary helper visibility from private to internal; do not alter implementations or callers.
5. Preserve full-rule labels/requirements needed for isolated part preparation.
6. Add lazy compilation cache and typed failures.

Suggested files:

```text
pattern/diff/automata/RuleCubeCompiler.kt
pattern/diff/automata/CompiledCube.kt
```

Acceptance: compiling a cube independently produces the same `TaintAutomataEdges` as the corresponding pipeline steps in a focused characterization fixture; exact matched cubes never call the compiler.

### Phase 4: synchronous automata diff

1. Normalize the graph from `TaintAutomataEdges.automata`.
2. Separate method predicates from strict binding guards/effects.
3. Normalize sparse generated-edge observations.
4. Implement SAT overlap, coverage, cache, deadlines, and unknown results.
5. Validate reachable determinism.
6. Implement deterministic product BFS with bottom states.
7. Compare terminal and generated-edge observations.
8. Add symbolic witness reconstruction and replay.

Suggested files:

```text
pattern/diff/automata/AutomataNormalizer.kt
pattern/diff/automata/GuardSolver.kt
pattern/diff/automata/SynchronousAutomataDiff.kt
pattern/diff/automata/TraceWitness.kt
pattern/diff/automata/TraceReplay.kt
```

Acceptance: `Equivalent` is returned only after exhausting the exact deterministic product; limits/nondeterminism return inconclusive; every difference witness replays.

### Phase 5: unmatched cube pairing and joins

1. Build the lazy old/new unmatched-cube candidate matrix.
2. Match compiled variants and contextual cubes with explicit dummies.
3. Combine exact and automata cube mappings and infer declaration mappings.
4. Compare parsed normal-rule roles, modifiers, counts, metadata, and options through that mapping.
5. Implement declared and resolved join structure diff.
6. Recursively apply normal-rule DNF/cube diff to resolved join operands.
7. Attribute automata results back to declarations and join items.

Suggested files:

```text
pattern/diff/CubeMatcher.kt
pattern/diff/structure/DeclarationMatcher.kt
pattern/diff/structure/StructuralRuleDiffer.kt
pattern/diff/JoinRuleDiffer.kt
pattern/diff/RuleDiffEngine.kt
```

Acceptance: join/taint changes are attributed without using list position; unchanged operand cubes do not compile in the diff path.

### Phase 6: reports and runner

1. Add versioned report DTOs.
2. Add deterministic text and JSON renderers.
3. Add `RuleDiffService`, selection, strict-load, and language validation.
4. Add JVM runner, `JavaExec` task, formats, output, and exit codes.
5. Add fat-jar classpath smoke tests.
6. Optionally add a Go CLI wrapper.

If JSON rendering stays in `opentaint-java-querylang`, add the `kotlinx-serialization-json` runtime dependency; the compiler plugin alone is insufficient. Otherwise keep JSON rendering in root `core`.

## 15. Test plan

### 15.1 Loader and compatibility

- No extension produces unchanged full-load result and diagnostics.
- Extension sees top-level and library normal rules.
- Declared and resolved join snapshots include tag expansion and overrides.
- Dependency-closure diagnostics are attributed correctly.
- Malformed YAML, duplicate IDs, disabled rule, unsupported language, and failed final conversion.
- Unrelated broken rule under strict and non-strict loading.
- Auto-selection when all other rules are library, disabled, or failed.
- Java and Go selection.

### 15.2 DNF and structural diff

- Same formula and reordered conjunction produce identical cube multisets.
- `pattern-either` produces multiple cubes under one declaration.
- Duplicate cubes retain multiplicity and cancel one-for-one.
- Added/removed source, sink, propagator, and sanitizer.
- Modifier, label, `requires`, focus, constraint, and propagator endpoint changes.
- One alternative changed: only that old/new cube remains.
- `$X` changed to `$Y`: structural difference and no exact cube match.
- Matching/taint mode change.
- File move changes qualified location but not short declared ID.

### 15.3 Lazy cube compilation

- Exact matched cube causes zero compiler calls.
- One unmatched pair causes one cached compile per side.
- Matching, source, sink, propagator, sanitizer, and join-side contexts.
- Source `requires` and full-rule label context.
- Language rewrite producing multiple compiled variants.
- Cube compilation failure returns typed inconclusive without affecting normal loading.

### 15.4 Automata comparison

- State IDs, predicate IDs, and insertion order differ only: equivalent.
- Split disjoint guards versus an equivalent union guard: equivalent.
- Broader/narrower guard: directional witness.
- Same trace ending accept versus dead: terminal difference.
- `$X` bind-and-reuse versus `$Y`: difference under strict names.
- Assignment position change: binding/effect difference.
- Same graph language but changed generated edge/global-state observation.
- Loop and bottom-state coverage behavior.
- Reachable overlapping guards: nondeterminism inconclusive.
- SAT timeout, unsupported constraint, and product limit: inconclusive, never equivalent.
- Added/removed cube compared with bottom: new/removed trace.

### 15.5 Join diff

- Ref/selector/alias/rename/operator/endpoint changes.
- Tag expansion member added/removed.
- Override target change.
- Operand reorder only.
- Unchanged operand cubes avoid compilation.
- Changed operand cube receives automata comparison.
- Join-to-join ref remains a load failure.

### 15.6 Reporting and integration

- Golden equivalent, changed, inconclusive, and load-failed JSON/text.
- Structural-only change with no trace difference.
- Changed plus unresolved comparison yields `CHANGED` and `comparisonComplete=false`.
- Deterministic repeated output.
- Selectors, stdout/stderr, formats, and exit codes `0/2/1`.
- Analyzer fat-jar classpath invocation.

Verification commands:

```bash
cd core
./gradlew :opentaint-java-querylang:test :opentaint-go-querylang:test
./gradlew test :projectAnalyzerJar

cd ../cli
go test ./...
```

## 16. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Loader extension changes normal behavior | Read-only optional callbacks only in loader orchestration; characterization tests with no extensions |
| DNF helper drifts from real conversion | Reuse the same NNF/DNF code and verify one-for-one against `convertToRawRule` |
| Per-cube compilation differs from full context | Preserve role and full-rule label context; compare against focused pipeline fixtures |
| Too many automata builds | Exact cube cancellation first, lazy per-run cache, build unmatched cubes only |
| Sparse edge lists are mistaken for a graph | Simulate `TaintAutomataEdges.automata`; treat edge lists as observations |
| State/register IDs differ | Compare state and assignment epochs through product correspondence |
| User metavariable rename is accidentally hidden | Strict name comparison in cube keys, binding normalization, and join structure |
| Nondeterminism yields a false proof | Return inconclusive in v1 |
| SAT/type operations are incomplete | Typed unknown/inconclusive; never equivalent on solver failure |
| Weak edited candidates are forced together | Explicit add/remove dummies and bounded edit costs |
| Load failure looks like removal | Require successful full-load snapshots and emitted rule on both sides |
| Hash iteration changes results | Canonical ordering and deterministic BFS/matching |

## 17. Completion criteria

The v1 implementation is complete when:

1. Both sides finish the unchanged full load using fresh loaders.
2. Read-only loader snapshots expose parsed normal/join structure and resolved dependencies.
3. Structural diff operates on `NormalRule<Formula>` semantics and DNF cube multisets.
4. Exact cubes are cancelled before any diff-specific automata compilation.
5. Only unmatched cubes are passed to the standalone cube compiler.
6. The standalone compiler reuses existing conversion functions without converter instrumentation.
7. Synchronous simulation uses `TaintAutomataEdges.automata` and preserves strict user-metavariable names.
8. Generated edge lists/global-state metadata are compared as observations.
9. Every proved trace divergence has a replay-validated symbolic witness.
10. Limits, nondeterminism, and unsupported solver operations return inconclusive rather than false equivalence.
11. Taint and join structure changes are deterministic, multiplicity-aware, and mapped back to declarations.
12. Existing loader/converter output remains compatible when diff extensions are absent.

## 18. Repository evidence

Key anchors:

- Public load result and orchestration: `SemgrepRuleLoader.kt:112-153`.
- Private parsed normal/join/override model: `SemgrepRuleLoader.kt:193-213`.
- Normal build entry: `SemgrepRuleLoader.kt:287-339`.
- Join resolution: `SemgrepRuleLoader.kt:401-465`.
- Formula model: `SemgrepYamlParsing.kt:317-328`.
- Taint formula parsing: `SemgrepYamlParsing.kt:420-446`.
- `convertToRawRule` and cube construction: `SemgrepYamlParsing.kt:463-580`.
- Existing private NNF/DNF implementation: `SemgrepYamlParsing.kt:598-643`.
- Action-list/automata build: `SemgrepRuleAutomataBuilder.kt:50-145`.
- Rule and taint-part structure: `SemgrepRule.kt:1-85`.
- Register automata creation: `TaintRegisterAutomataCreation.kt:34-48`.
- Role preparation: `TaintRuleProcessing.kt:225-399`.
- `TaintAutomataEdges` generation: `TaintAutomataGeneration.kt:38-46`.
- Sparse generated-edge selection: `TaintEdgesGeneration.kt:32-171`.
- `TaintAutomataEdges` representation: `TaintAutomataEdges.kt:5-36`.
- Register-state semantics: `TaintRegisterStateAutomata.kt:9-64`.
- Predicate-manager allocation: `MethodFormulaManager.kt:8-31`.
- Existing Boolean SAT entry: `MethodFormulaSimplifier.kt:69-86`.

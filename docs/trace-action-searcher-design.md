# Trace action searcher design

Date: 2026-07-23

## Status

Proposed design for implementing
`TaintAnalysisUnitRunnerManager.collectActionableRules` in
`TraceActionSearcher.kt`.

## Goal

The shallow scan must identify the configuration entries that are sufficient
to reproduce each resolved vulnerability in the full scan. Across every
trace branch that can participate in a complete source-to-sink path, the
searcher must collect:

1. the sink rule represented by the vulnerability, with an empty action set;
2. every rule and its actions carried by an `otherAction` in the relevant
   trace;
3. source rules and actions hoisted into a `SourceStartEntry`;
4. rules and actions inside every expanded `CallSummary`; marked summaries
   must expand, while all-abstract/unmarked summaries must be skipped.

Change `Collected.rules` to expose a
`Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>`. An empty action
set denotes a sink rule. A non-empty action set contains every used action for
that rule.

The searcher does not prove the vulnerability again. `TraceResolver` has
already built the interprocedural source-to-sink graph. The searcher identifies
the graph corridor that belongs to at least one complete source-to-sink path,
materializes its `FullStart2FinalTrace` objects, expands relevant inner
summaries, and projects all relevant entries to the rule/action map.

## Non-goals

- Do not enumerate source-to-sink or intra-method path combinations. Traverse
  every entry in every relevant full trace and recursively traverse every
  relevant summary. The required result is a union, so path enumeration adds
  combinatorial cost without adding information.
- Do not collect rules from entry-point-to-start traces. The selected rules
  describe taint creation and propagation from source to sink, not ordinary
  reachability from an application entry point.
- Do not expand structural summaries whose boundary facts are all abstract
  and unmarked.
- Do not infer markedness from AP implementation classes, `isAbstract()`, or
  from `SourceTraceEdge` versus `MethodTraceEdge`.
- Do not make path order part of the result contract.

## Existing model

### Trace representations

`MethodTraceResolver` has three relevant representations:

| representation | contents | use |
|---|---|---|
| `SummaryTrace` | method, final entry, trace kind | lazy request for an intra-method trace |
| `Start2FinalTrace` | method, selected start, final, trace kind | compact interprocedural graph node |
| `FullStart2FinalTrace` | entry array, start/final IDs, successor graph | materialized intra-method witness |

`TraceResolver.Trace.sourceToSinkTrace` connects compact
`Start2FinalTrace` nodes. `trace/path/Source2SinkTraceGraph.kt` separates the
root-to-source and root-to-sink directions.
`trace/path/TracePath.kt` shows how compact nodes are converted to
`FullStart2FinalTrace` objects.

The action searcher should reuse those graph-building and full-resolution
operations. It should not use the reporting path sampler as its semantic
oracle: the sampler intentionally selects representative paths and one
intra-method route, while full-scan rule selection must not omit a relevant
alternative.

### Rule-bearing entries

`TraceEntry.Action` contains a primary action, a set of other actions, and
unchanged edges. The rule-bearing other-action variants are:

| action | rule type | action type |
|---|---|---|
| `SequentialSourceRule` | `CommonTaintConfigurationSource` | `Set<CommonTaintAssignAction>` |
| `CallSourceRule` | `CommonTaintConfigurationSource` | `Set<CommonTaintAssignAction>` |
| `EntryPointSourceRule` | `CommonTaintConfigurationSource` | `Set<CommonTaintAssignAction>` |
| `CallRule` | `CommonTaintConfigurationItem` | `Set<CommonTaintAction>` |

`MethodTraceResolver.tryCreateSourceStart` converts a source-only
`TraceEntry.Action` to `TraceEntry.SourceStartEntry`. Therefore collection
must inspect both:

```text
TraceEntry.Action.otherActions
TraceEntry.SourceStartEntry.sourceOtherActions
```

Inspecting only `TraceEntry.Action` would silently lose source rules.

The primary action variants do not directly contribute rule/action map data:

- `Sequential` and `UnresolvedCallSkip` are structural;
- `CallSourceSummary` points to the source-producing callee trace;
- `CallSummary` points to an optionally relevant inner callee trace.

### Vulnerability rule provenance

`TaintVulnerability` contains a map of sink rules to vulnerability rule
nodes. Trace resolution walks the node values but does not retain which map
key produced the selected trace. Consequently
`TaintVulnerability.rule`, which returns the first map key, is not reliable
when multiple sink rule objects were merged under the same vulnerability ID.

The safe current behavior is:

```text
for every vulnerability.vulnerabilityRules key:
    collect sink rule -> emptySet()
```

This is a small overapproximation. If exact sink-rule provenance becomes
important, `TraceResolutionRequest` and `TraceResolver.Trace` must carry the
originating sink rule. Selecting the first map key is not an acceptable
substitute.

## Relevant-entry specification

### Vulnerability sink

Every sink rule attached to the vulnerability is relevant. Emit one map entry
per rule:

```text
sinkRule -> emptySet()
```

An empty set is reserved for sink rules. A trace-derived rule must have a
non-empty action set.

### Other actions

For every rule-bearing other action in the relevant trace, union its action
set into the map value for its rule:

```text
RuleAction(rule = R, actions = {A1, A2})
    -> R -> {A1, A2}
```

The rule is the map key and actions deduplicate within its set. Repeated uses
of the same rule accumulate their action sets:

```text
R -> {A1}
R -> {A2}
    becomes
R -> {A1, A2}
```

The representation assumes that a configuration item cannot be both a sink
rule and an action-owning source/pass rule. Enforce this invariant while
building and consuming the map; otherwise `emptySet()` would be ambiguous.

### `CallSourceSummary`

`CallSourceSummary` carries no direct rule/action map contribution.

When it appears as the primary action of a `SourceStartEntry` in a full trace
materialized from an outer compact node, `TraceResolver` has created the
corresponding `CallToSource` interprocedural edge. The relevant-node corridor
includes the callee as a separate method trace. Its source and propagation
actions are therefore collected in their normal entries.

In other words:

```text
CallSourceSummary in SourceStartEntry
    -> no direct map contribution
    -> for an outer compact model, callee already appears on root-to-source
       graph corridor
```

If the callee cannot be resolved, that source branch is invalid. It must be
pruned before the outer corridor is recomputed; the searcher must not silently
treat the caller entry as a complete source.

There is one distinct case. `MethodTraceResolver.tryCreateSourceStart` does
not hoist a source action when the same entry also has unchanged edges or
when any sibling other action is not a `SourceOtherAction`. A
`CallSourceSummary` can therefore remain the primary action of an ordinary
`TraceEntry.Action`.

The user's intended invariant is that this action is already on the
source-to-sink path. That is true for the caller action entry, but the current
interprocedural graph does not add a `CallToSource` callee node for an
internal action; it recognizes only a `SourceStartEntry` primary summary.
This design chooses an explicit compatibility path: resolve the internal
action's `summaryTrace` as an inner full trace. This does not duplicate the
`SourceStartEntry` case because the two entry variants are mutually
exclusive. A future trace-model change may represent every such source call
interprocedurally and then remove this fallback.

A `SourceStartEntry.CallSourceSummary` found while recursively materializing
an inner summary is different: that inner model has no node in the outer
interprocedural graph. Treat its source summary as a required inner dependency
and resolve it recursively.

### `CallSummary`

`CallSummary` also carries no direct map contribution. Its `summaryTrace` is expanded when
the callee summary boundary contains a taint mark, skipped when every boundary
fact is abstract and unmarked, and expanded conservatively for the remaining
concrete-unmarked case.

The classification is based on `callSummary.summaryTrace.final.edges`, not on
the caller-side `callSummary.summaryEdges`. A caller-side
`TraceSummaryDelta` may carry a mark while the callee summary itself operates
only on an abstract structural fact. Expanding such a summary would collect
unrelated rules.

For a `TraceEdge`, its complete boundary fact set is:

```text
SourceTraceEdge       -> { fact }
MethodTraceEdge       -> { initialFact, fact }
MethodTraceNDEdge     -> initialFacts union { fact }
```

A summary operates on taint marks exactly when at least one boundary fact of
its final entry satisfies:

```kotlin
fact.getAllAccessors().any { it is TaintMarkAccessor }
```

Both input and output facts are required because a summary can create, carry,
or remove a mark.

`FactAp.isAbstract()` is not the markedness predicate. A fact may be abstract
and still carry a mark in the general Tree or Automata domain.

| summary boundary | decision |
|---|---|
| concrete or abstract fact with a taint mark | resolve inner full trace |
| every boundary fact is abstract and no fact has a mark | skip inner trace |
| any concrete boundary fact and no fact has a mark | resolve conservatively |

The user explicitly permits skipping abstract facts without marks. A
concrete-unmarked summary is not covered by that permission. Resolving it is
the sound default until the trace model proves that this state is impossible
or gives it separate semantics.

```text
EXPAND if any boundary fact has TaintMarkAccessor
SKIP   if all boundary facts are abstract and none has a mark
EXPAND otherwise
```

## Proposed pipeline

The implementation has two conceptual layers:

```text
trace extraction:
    VulnerabilityWithInterproceduralTrace
        -> relevant (MethodEntryPoint, TraceEntry) stream

rule projection:
    relevant TraceEntry stream
        -> Map<Rule, Set<Action>>
```

Keep these layers independently testable. The production implementation may
stream entries directly into the projector rather than retaining a large
intermediate list.

Traversal completeness is defined structurally:

```text
for every relevant FullStart2FinalTrace:
    visit every element of entries
    enqueue every relevant SummaryTrace referenced by those entries

for every distinct enqueued SummaryTrace:
    resolve every FullStart2FinalTrace
    apply the same traversal
```

No source-to-sink path list or intra-method entry path is constructed.

### 1. Validate and seed

Create a per-invocation mutable map from rules to mutable action sets and seed
it with every vulnerability sink rule mapped to an empty set.

Then classify the interprocedural trace:

| input | result |
|---|---|
| `trace == null` | `Failed` |
| simple unconditional trace | `Collected(sink rule map)` |
| non-simple source-to-sink trace | continue |

The simple case has no source-to-sink action trace to inspect.

### 2. Build the relevant interprocedural corridor

Handle a `SimpleTraceNode` before calling
`createSource2SinkGraph`, whose current contract expects interprocedural
roots.

For a non-simple trace, call `createSource2SinkGraph` and compute nodes that
belong to at least one complete path without enumerating paths.

First compute terminal reachability in reverse and retain only roots that can
reach both sides:

```text
canReachSource = reverse reachability from sourceNodes
canReachSink   = reverse reachability from sinkNodes
completeRoots = rootNodes intersect canReachSource intersect canReachSink
```

Then, for each direction, compute:

```text
forwardReachable  = nodes reachable from completeRoots
backwardReachable = canReachSource or canReachSink
corridor          = forwardReachable intersect backwardReachable
```

Use the following adjacency:

| direction | forward adjacency | backward adjacency | terminal set |
|---|---|---|---|
| root to source | `root2SourceFwd` | `root2SourceBwd` | `sourceNodes` |
| root to sink | `root2SinkFwd` | `root2SinkBwd` | `sinkNodes` |

If `completeRoots` is empty, collection fails. Otherwise, the relevant
interprocedural node set is the union of the source and sink corridors. Each
retained action can therefore participate in at least one complete half-path,
and each retained root is connected to both a source and a sink.

This union is required for sound staged rule selection. BaseOnly can expose
several shallow alternatives, including spurious ones. Selecting only the
first witness could collect rules for a spurious branch and omit the rules for
a real branch that Tree can reproduce in the full scan.

At this point the corridor is a topological candidate corridor. Inner-summary
validity can still invalidate an action entry or an entire compact node.
Recompute the corridor after the dependency fixed point in step 5.

### 3. Materialize trace models and discover dependencies

For every compact interprocedural node in the corridor, use the same
operations as `TracePath.kt`:

```text
InterProceduralStart2FinalTraceNode
    -> resolveIntraProceduralFullStart2FinalTrace(Start2FinalTrace, ...)

InterProceduralSummaryTraceNode
    -> resolveIntraProceduralFullStart2FinalTrace(SummaryTrace, ...)
```

Resolution must run through `withMethodRunner(node.methodEntryPoint)`. Set
`collapseUnchangedNodes = true`; collapsing unchanged nodes preserves all
action entries and reduces memory.

Traverse the complete `FullStart2FinalTrace.entries` array for every
materialized trace. Do not enumerate routes through `successors`.
`MethodTraceResolver` has already removed entries that are unreachable from
the selected start/final trace. The successor graph is used only for
reachability after an invalid summary dependency is pruned.

Represent each returned full trace as a small dependency model:

```text
ResolvedTraceModel:
    entries
    start ID
    final ID
    successors
    optional inner SummaryTrace dependency per action entry
```

An entry has a dependency when its primary action is:

- a marked `CallSummary`;
- a concrete-unmarked `CallSummary`, resolved conservatively;
- an internal `CallSourceSummary`.

An abstract-unmarked `CallSummary` has no dependency.

Dependency extraction is context-sensitive for
`SourceStartEntry.sourcePrimaryAction`:

| full-trace model origin | `SourceStartEntry.CallSourceSummary` |
|---|---|
| outer compact interprocedural node | represented by outer `CallToSource` edge; no local dependency |
| recursively discovered inner summary | required local `SummaryTrace` dependency |

Discover dependencies with an invocation-local `SummaryTrace` worklist.
Resolve each distinct relevant summary key once with the strict
full-resolution API, traverse every entry of every returned full trace, and
store all returned full-trace models. Enqueue every relevant dependency found
in those entries. This discovery terminates on recursive call graphs because
keys are marked discovered before their full traces are inspected.

`Cancelled` or `HardLimit` aborts the entire collection invocation with
`Failed`. Never convert a strict partial-resolution result to an invalid
summary model. Only `Complete(emptyList())` represents a semantically invalid
alternative that the fixed point may prune.

Do not update the rule/action map during discovery. Some discovered traces and
entries may later prove to be dead alternatives.

`InterProceduralSummaryTraceNode` should be supported by the materializer for
completeness, but current `TraceResolver` does not construct this node type at
runtime.

### 4. Classify inner-summary validity by least fixed point

Use the summary-boundary mark predicate above. Do not use the current default
`InnerCallTraceResolveStrategy` predicate:

```text
SourceSummary -> true
MethodSummary -> edge.fact != edgeAfter.fact
```

The default answers whether a call changes an edge, not whether the callee
summary operates on a taint mark.

Summary validity is a positive Boolean fixed point:

```text
entryValid(E, V) =
    E has no inner dependency
    or dependency(E) is in valid-summary set V

traceValid(T, V) =
    T has a start-to-final path containing only entryValid entries

summaryValid(S, V) =
    any full trace of S satisfies traceValid(T, V)
```

Compute the least fixed point incrementally:

```text
1. Build a reverse index:
       dependency SummaryTrace -> dependent trace entries
2. Enable every entry with no dependency.
3. In each trace model, propagate reachability from its enabled start through
   enabled entries.
4. When a trace final becomes reachable, mark its owning summary valid.
5. When a summary becomes valid, enable its dependent entries and continue
   reachability propagation.
6. Stop when the worklist is empty.
```

This gives the required recursive semantics:

- a non-recursive base path seeds validity;
- a recursive SCC with a path to a valid base becomes valid;
- a pure recursive SCC with no finite base path remains invalid.

Merely marking a recursive summary “processed” is not enough: it would
incorrectly accept a cycle that has no finite trace.

For any full trace and final valid-summary set, compute the relevant entry
corridor using only valid entries:

```text
reachableFromStart(valid entries)
    intersect
canReachFinal(valid entries)
```

An invalid alternative is pruned. It does not make a sibling valid alternative
fail, and its `otherActions` are not projected.

### 5. Validate the outer graph and project relevant entries

An outer compact node is valid when at least one of its full-trace models has
a valid start-to-final path under the final summary-validity set.

Remove invalid compact nodes and their incident interprocedural edges, then
recompute `completeRoots`, root-to-source corridor, and root-to-sink corridor
as in step 2. If no complete root remains, return `Failed`.

For every valid full trace of every node in the recomputed outer corridor,
iterate all entries and project each entry retained by its valid
start-to-final corridor. Then traverse every valid relevant inner summary
referenced by those entries, again iterating all of its full-trace entries.
Inner projection uses a visited-summary set only for deduplication; validity
has already been solved by the fixed point.

Thus the algorithm traverses entries and summary graphs, not paths. The
reachability sets are Boolean filters over entries; they are never enumerated
as path sequences.

For each projected entry:

- inspect `Action.otherActions`;
- inspect `SourceStartEntry.sourceOtherActions`;
- ignore `Unchanged`, `Final`, `MethodEntry`, and structural primary actions.

Ordering is not part of result equality.

### 6. Freeze and return

For each projected `RuleAction`, union all of its actions into the mutable set
stored under its rule. Preserve different rule objects that happen to share an
ID unless the rule configuration layer explicitly defines them as equal.

Sink rules remain mapped to an empty set. Reject an attempt to add actions to
a sink-rule key or to register an action-owning rule as a sink.

Create immutable snapshots of both the outer map and every inner action set,
then return `Collected(rules)`.

## Required strict full-resolution status

The current
`resolveIntraProceduralFullStart2FinalTrace` API returns a list even when its
`TraceBuilder` stopped because cancellation became inactive or the action hard
limit was reached. Such a list can be a partial trace. The action searcher
cannot distinguish it from a complete result and could incorrectly return a
partial `Collected`.

Add a strict resolution API, or strengthen the existing one, to return:

```kotlin
sealed interface FullTraceResolutionResult {
    data class Complete(
        val traces: List<FullStart2FinalTrace>,
    ) : FullTraceResolutionResult

    data object Cancelled : FullTraceResolutionResult
    data object HardLimit : FullTraceResolutionResult
}
```

`TraceBuilder.resolveTrace` must report why its worklist loop stopped:

- empty worklist -> complete;
- inactive cancellation -> cancelled;
- action limit -> hard limit.

An empty trace list from a completed resolution means that no matching full
trace exists. It makes that outer node or inner summary invalid. Collection
fails only if pruning invalid models leaves no complete outer path.

The reporting path may retain a best-effort adapter if needed, but
`TraceActionSearcher` must use the strict result.

## Model cleanup

Introduce a common semantic interface for rule-bearing actions:

```kotlin
sealed interface RuleAction : TraceEntryAction {
    val rule: CommonTaintConfigurationItem
    val action: Set<CommonTaintAction>
}

sealed interface CallRuleAction : CallAction, RuleAction
```

Make `SequentialSourceRule` implement `RuleAction`; the three existing call
rule variants continue through `CallRuleAction`. Kotlin's read-only `Set`
covariance permits source actions to retain their narrower action element
types.

Then the collector has one projection:

```text
RuleAction(rule, actions)
    -> result.getOrPut(rule, ::mutableSetOf).addAll(actions)
```

This is preferable to a type switch in `TraceActionSearcher`: adding another
rule-bearing action without implementing `RuleAction` becomes a model-level
review error instead of a silent collector omission.

The map contract is:

```kotlin
data class Collected(
    val rules: Map<CommonTaintConfigurationItem, Set<CommonTaintAction>>,
) : ActionableRulesCollectionResult
```

An empty value set identifies a sink rule. All other entries have non-empty
value sets.

## Failure contract

Return `Failed` for:

- a missing interprocedural trace;
- a non-simple trace with no complete source-to-sink path;
- no complete outer path after invalid inner-summary alternatives are pruned;
- cancellation, a trace-resolution hard limit, or an unexpected trace-model
  invariant violation.

Do not return `Failed` merely because:

- a `CallSummary` is unmarked;
- an entry has no rule-bearing other actions;
- a `CallSourceSummary` has no direct map contribution;
- an action was already present in the rule's action set.

The current shallow-scan consumer drops `Failed` discoveries. Therefore
failure must never be converted to a partially collected result.

## Downstream full-scan contract

`Phase.FullScan` currently receives the per-vulnerability `Collected` values,
while the JVM and Go consumers are still TODO. They should merge all maps
globally before configuring the full scan:

```text
for each (rule, actions):
    if rule is absent:
        copy actions
    else:
        union actions into the existing set
```

Map interpretation is exact:

```text
sink rule -> emptySet()       -> enable that sink rule
rule      -> {A1, A2, ...}    -> enable exactly those actions for that rule
```

An empty action set is not a wildcard. Source and pass rules require non-empty
sets. Assert that no merge combines an empty sink value with a non-empty
action value for the same rule.

## Concurrency and lifetime

Actionable-rule resolution processes vulnerabilities in parallel. All mutable
search state must be invocation-local:

- rule-to-mutable-action-set map;
- discovered summary models;
- valid-summary fixed-point set;
- projection visited-summary set;
- interprocedural and intra-method reachability worklists.

Method runners and their trace stores remain shared, read-only inputs under
the existing trace-resolution concurrency contract. Do not introduce a
global summary-resolution cache in the first implementation: it would need
publication, cancellation, and AP-manager lifetime rules that are unnecessary
for correctness.

The returned map and its action sets must not expose mutable collector state.

## Complexity

With the incremental reverse-dependency worklist, and excluding the cost
inside `MethodTraceResolver`, collector-side traversal is:

```text
O(source-to-sink graph nodes and edges
  + all materialized full-trace entries and edges
  + inner-summary dependency references)
```

`collapseUnchangedNodes = true` and per-invocation summary deduplication are
the primary cost controls. No Cartesian product of source-to-sink alternatives
is required. Each summary changes to valid at most once, each dependent entry
is enabled at most once, and each reachability edge is propagated at most
once.

Full-trace materialization itself can explore action combinations not present
in the returned graph and is guarded by the resolver action hard limit. Its
cost must be measured separately with existing trace-resolver step counters.

Useful counters are:

- outer graph nodes retained and pruned;
- full traces materialized;
- action entries visited;
- marked inner summaries resolved;
- abstract-unmarked inner summaries skipped;
- summary dependency cycles discovered;
- distinct rules and actions emitted;
- failure reason.

## Rejected alternatives

### Use `generateTracePath` with `limit = 1`

This is attractive because it already materializes full traces, but it is an
underapproximation for staged rule selection. A BaseOnly-only shallow branch
can be selected while a different branch contains an action needed under a
rule by a real Tree/full-scan path. The graph-corridor union is linear and
avoids that omission without enumerating path combinations.

### Collect every node reachable from a root

Forward reachability alone includes dead source or sink branches. Intersecting
forward and backward reachability retains only nodes that can reach the
corresponding terminal.

### Classify a call using `summaryEdges`

Those are caller-side facts and deltas. They can contain a mark even when the
callee `SummaryTrace` operates only on unmarked structural facts. The callee
final boundary is authoritative.

### Classify a call using only `FactAp.isAbstract()`

Abstractness and markedness are independent in the general AP contract.
Markedness must be checked first with `TaintMarkAccessor`; abstractness is
then used only to recognize the explicitly skippable all-abstract/unmarked
case.

### Apply a fixed inner-summary depth limit

A fixed limit terminates recursion by silently omitting deeper rules or
actions. Deduplicating `SummaryTrace` keys terminates dependency discovery;
the least-fixed-point validity solver then preserves finite-path semantics
and rejects recursive SCCs without a valid base route.

## Verification plan

### Fact and summary classification

Test the mark predicate independently for Tree and BaseOnly facts:

- mark only on `SourceTraceEdge.fact`;
- mark only on `MethodTraceEdge.initialFact`;
- mark only on `MethodTraceEdge.fact`;
- mark on one `MethodTraceNDEdge.initialFacts` member;
- mark only on the ND output fact;
- abstract fact with a mark is relevant;
- abstract fact without a mark is irrelevant;
- concrete fact without a mark is expanded conservatively;
- caller-side delta has a mark but the callee final boundary is entirely
  abstract and unmarked: irrelevant.

The last case pins the distinction between `summaryEdges` and
`summaryTrace.final.edges`.

### Entry projection

Test:

- every vulnerability sink rule maps to `emptySet()`;
- one other action with multiple actions produces one rule key with all
  actions;
- repeated actions deduplicate within the rule's action set;
- repeated uses of the same rule union their different actions;
- all four current rule-bearing other-action variants;
- source rules in `SourceStartEntry.sourceOtherActions`;
- structural primary actions add no map contribution;
- sink/action key collisions fail the representation invariant;
- map equality is independent of insertion and hash-iteration order.

### Trace scenarios

Add small dataflow samples for:

1. a simple unconditional vulnerability: sink rule only;
2. sequential source -> pass rule -> sink;
3. source in a callee represented by `CallSourceSummary`: callee source rule is
   obtained from the interprocedural source path;
4. marked `CallSummary`: its inner rule and action are collected;
5. unmarked abstract `CallSummary`: inner trace is not resolved and its rules
   are not collected;
6. marked inner summary with an unresolvable first route and a valid second
   route: rules and actions from the valid resolved route are retained;
7. recursive marked summary: collection terminates and returns each rule with
   its complete deduplicated action set;
8. missing trace and fully unresolvable marked summary: `Failed`;
9. merged vulnerability sink rules: all sink keys are retained;
10. alternate source and sink branches: collect the union from every branch
    in the complete-path corridor, but not from dead branches;
11. `CallSourceSummary` retained in an ordinary `Action` because of unchanged
    edges or a non-source sibling action: resolve and collect its inner source
    rule;
12. pure recursive inner-summary SCC: it is invalid without a finite base
    path and becomes valid when a base alternative is added;
13. marked `CallSummary` -> inner `SourceStartEntry.CallSourceSummary` ->
    deeper source: collect the deeper source rule and invalidate the route if
    the deeper summary has no finite trace;
14. cancellation and action-hard-limit exits after partial graph construction:
    return `Failed`, never `Collected`.

Each scenario should assert the exact rule-to-action-set map, not only success.

### Integration

Run a staged JVM and Go analysis where the full-scan rule provider is filtered
by the collected rule/action maps. Assert:

- a true shallow branch is reproducible by the full scan;
- a shallow BaseOnly-only false discovery can disappear in the full scan;
- an unmarked structural helper does not cause unrelated rules to be enabled;
- Tree and BaseOnly collect compatible rule/action supersets for equivalent
  semantic trace graphs.

### Regression gates

Run the full dataflow and both query-language suites. Add a workload with
nested and recursive summaries and assert structural counters rather than
wall-clock timing:

- topologically dead outer branches are pruned before full-trace resolution;
- each distinct expanded `SummaryTrace` is fully resolved at most once per
  vulnerability;
- abstract-unmarked summaries cause no inner full-trace resolution.

## Implementation sequence

1. Add `RuleAction` and the summary-boundary mark helpers with unit tests.
2. Add the strict full-trace resolution result and partial-resolution tests.
3. Extract/reuse source-to-sink graph construction and add corridor
   reachability tests.
4. Implement dependency discovery, least-fixed-point validity, and valid
   full-trace corridor traversal.
5. Implement `collectActionableRules` failure, simple-trace, graph-validity,
   and projection handling.
6. Add end-to-end staged-analysis tests for JVM and Go.
7. Add counters and rerun the full dataflow/query-language test suites.

## Acceptance criteria

The feature is complete when:

1. every `Collected` result comes from a resolved source-to-sink graph with at
   least one complete source-to-sink path;
2. it contains every vulnerability sink rule and every action grouped under
   its rule from every relevant graph branch, including marked inner
   summaries;
3. it contains no rule or action solely from an abstract-unmarked inner
   summary;
4. recursive summaries terminate without a semantic depth cutoff;
5. cancellation or a hard-limit partial resolution returns `Failed`, while a
   semantically invalid alternative is pruned;
6. full scan configured from the collected maps does not lose a real branch
   merely because BaseOnly also exposed a different shallow alternative;
7. JVM, Go, dataflow, and query-language regression suites remain green.

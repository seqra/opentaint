# Conductor BaseOnly trace-resolution mitigation plan

## Verdict

The Conductor timeout is caused by **eager multiplication of observable action
alternatives with backward continuation states** in `MethodTraceResolver`.

The resolver does not visit one `TraceEntry` repeatedly. Instead, it constructs
millions of distinct call-summary/action alternatives which project to a much
smaller set of `(statement, edges)` continuations. It then repeats the same
backward transfer work for every alternative.

This is not primarily a summary-storage lookup, virtual-call lookup, or one
exceptionally large Cartesian-product problem. Those operations are visible in
profiles because they are repeated under the multiplied state space.

## Phase boundary

`TaintAnalyzer#resolveActionableRules` first calls
`resolveVulnerabilityInterProceduralTraces(resolveAllTraces = true)` and only
then calls `resolveVulnerabilityActionableRules`.

On the reference run:

- prescan: about 24.2 seconds;
- shallow forward scan: about 31.6 seconds;
- start-to-final/inter-procedural trace resolution: remained at 2/19 items for
  about 61 seconds and timed out;
- actionable-entry search did not become the active workload before timeout
  cleanup.

Therefore the current bottleneck precedes `TraceActionSearcher` and full action
rule evaluation.

## Concrete evidence

The instrumented Conductor run processed 5,784 trace builders and recorded:

| quantity | count |
|---|---:|
| raw call choices | 104,330 |
| merged call/target alternatives | 1,705,232 |
| resolved call-summary alternatives | 8,602,938 |
| selected summary alternatives | 2,510,609 |
| emitted predecessors | 8,602,938 |
| distinct `(statement, edges)` continuations | 115,295 |

The resolved alternatives therefore contain a **74.6× continuation
multiplicity**. Selected summaries alone contain a **21.8× multiplicity**.

A representative hot builder had:

```text
edges=20
rawChoices=17
merged=287
resolved=1451
selectedSummaries=420
hotPredecessors=1451
emittedContinuationKeys=20
```

Another had 25 facts, 481 merged alternatives, 3,282 resolved alternatives,
1,365 selected summaries, and only 26 continuation keys.

One concrete call is:

```text
%111 = %10.scheduleNextIteration(%12, %11, %13)
```

BaseOnly wildcard facts such as `var(31).*/{}`, `var(30).*/{}`, and
`var(85).*/{}` match summaries from seven exit statements. For example:

- `var(31).*/{}`: 124 resolved summaries, 19 selected;
- `var(30).*/{}`: 80 resolved summaries, 19 selected;
- `var(85).*/{}`: 22 resolved summaries, 8 selected.

Marked field variants match still more exact summary alternatives while many of
them produce the same predecessor edge set.

Thread dumps during the timeout show all workers allocating or comparing these
states in:

- `MethodTraceResolver#mergeCallActions`;
- `MethodTraceResolver#resolveCallPassSummary`;
- `MethodTraceResolver#selectWeakestEntries`;
- `MethodTraceResolver#containsEntryEdge`;
- `MethodTraceResolver.EntryManager#entryId`;
- `JIRCallResolver` target/context resolution.

This distributed profile is consistent with multiplicative state construction:
no single operation owns the entire cost.

## Incorrect representation boundary

The exact observable action identity is:

```text
(statement, unchanged edges, primary action, other actions)
```

Different alternatives must remain correlated because their nested summary,
rules, unchanged edges, and validity may differ.

The backward transfer identity is only:

```text
ContinuationKey(statement, predecessor edges)
```

`MethodTraceResolver#mergeCallActionsCombinations`,
`MethodTraceResolver#resolveCallSummary`, and
`MethodTraceResolver#addPredecessorActions` currently enumerate action
alternatives first and immediately materialize their predecessor entries. This
lets action provenance multiply the reachability state even though backward
transfer depends only on `ContinuationKey`.

The correct separation is:

```text
exact action alternatives  --many-to-one-->  continuation
continuation               --computed once--> predecessor continuations
```

The public full trace must still contain every relevant `TraceEntry.Action`.
Only the internal transfer computation is shared.

## Rejected local mitigations

The following prototypes all retained the 2/19 timeout:

1. globally canonicalizing action entries by `(statement, edges)`;
2. partitioning call-summary products by common exit before merging;
3. a start-only continuation dynamic program inside summary resolution;
4. per-resolver caches for call targets and resolved call summaries.

The first prototype is also not generally safe: globally merging observable
action nodes can mix their successor incidence. The third acted too late and
could not avoid construction in the surrounding call/action pipeline.

These experiments rule out a late deduplication or cache-only mitigation.

## Proposed representation

### 1. Intern edge sets and continuations

Introduce internal identifiers:

```kotlin
@JvmInline
value class EdgeSetId(val value: Int)

data class ContinuationKey(
    val statement: CommonInst,
    val edges: EdgeSetId,
)
```

`TraceBuilder` processes each `ContinuationKey` once. It records all observable
action emissions attached to that continuation, but does not enqueue each
action as an independent transfer state.

### 2. Preserve exact action alternatives

Keep the public representation:

```kotlin
TraceEntry.Action(statement, edges, actionId)
FullStart2FinalTrace.actionVariants[actionId]
```

For each successor entry, group exact variants only by the continuation edge
set. Do not merge action nodes belonging to different successor incidences.

Internally record:

```kotlin
data class PendingActionEmission(
    val successorId: Int,
    val continuation: ContinuationKey,
    val variants: Set<ActionVariant>,
)
```

After reachability is known, materialize the public graph as:

```text
predecessor -> Action(variants) -> successor
```

Internal continuation nodes must not appear in `FullStart2FinalTrace`.

### 3. Build call actions as a symbolic choice DAG

Replace eager Cartesian-product lists with a layered family:

```kotlin
data class ChoiceNodeKey(
    val layer: Int,
    val mode: PropagationMode,
    val continuationEdges: EdgeSetId,
)

enum class PropagationMode {
    Neutral,
    SourceOnly,
    NonSource,
}
```

Each transition retains the exact selected rule/summary action. Nodes with the
same layer, mode, and accumulated continuation share the remaining suffix
computation.

Apply this to:

- call-edge combinations;
- dynamic callee/entry-point choices;
- call-summary choices;
- rule-action choices;
- sequential action combinations.

Summary alternatives may be normalized by
`(callee, exit statement, summary edges, final edges)`. Alternatives from
different exit statements must never be merged.

### 4. Materialize only reachable family paths

For start-to-final resolution, traverse continuation reachability without
materializing action payloads.

For full resolution:

1. determine reachable continuation/family nodes;
2. enumerate exact variants only for reachable family paths;
3. assign `actionId`s and populate `actionVariants`;
4. insert observable action entries between their shared predecessors and exact
   successors;
5. remove all internal continuation/family nodes.

There must be no bypass edge around an action. Otherwise invalid nested-summary
filtering could incorrectly preserve a path.

## Correctness tests

Before enabling the new representation, compare it with exhaustive resolution
on bounded samples:

1. exact set of `ActionVariant` values;
2. exact start entries and final entry;
3. exact public adjacency after internal-node removal;
4. source-only, pass-only, mixed source/pass, and unresolved-call cases;
5. variants with identical continuations but different rules or nested
   summaries;
6. invalid nested summary in only one variant;
7. multiple callees and multiple exit statements;
8. ND facts and cyclic control flow;
9. sequential action combinations;
10. no internal node in `FullStart2FinalTrace`.

The current BaseOnly trace-entry explosion sample should additionally assert
that equivalent continuations are processed once while all action variants
remain present.

## Performance acceptance

Add per-phase counters:

```text
raw alternatives
symbolic choice nodes
continuation keys processed
reachable action variants materialized
public trace entries
peak resolver memory
```

The Conductor acceptance criteria are:

1. all 19 actionable-rule traces resolve within the existing timeout;
2. actionable rules and findings match the exhaustive implementation;
3. continuation processing is close to the measured 115,295-key quotient, not
   the 8.6-million resolved-alternative count;
4. full resolution materializes every reachable action variant required by the
   API;
5. core and both query-language suites remain green.

## Experimental validation of the plan

The probe validates the plan's central quotient: 8,602,938 exact alternatives
map to 115,295 continuation keys, so sharing backward transfer at that boundary
removes the measured 74.6× redundant dimension without deleting action
semantics.

The rejected prototypes validate the required placement: deduplication after
action construction and cache-only changes do not affect the timeout. The
sharing must therefore happen before eager action/summary materialization and
must be carried through the full-trace representation.

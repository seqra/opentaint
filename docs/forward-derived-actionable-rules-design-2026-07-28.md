# Forward-derived actionable-rule selection

## Goal

Replace shallow-scan trace resolution as the mechanism that selects rules for
the full scan. The forward analysis already evaluated every source rule/action
that can contribute a fact. Recording those successful applications is much
cheaper than reconstructing all action-bearing traces.

The effective full-scan selection contract is:

```text
Map<statement, Map<rule, Set<action>>>
```

Sinks use an empty action set. Today `SelectedTaintRulesProvider` filters source
rules and sinks with this map. Pass-through and cleaner rules are delegated and
therefore do not need selection provenance yet.

## Experimental implementation

The experiment is disabled unless the JVM property
`opentaint.experimental.forward-actionable-rules=true` is set. It does not
change production rule selection.

`ForwardActionableRulesRecorder` is owned by each
`TaintAnalysisUnitStorage`. Its state is cleared together with facts,
summaries, and vulnerabilities by `resetApManager`. All unit snapshots are
merged by `TaintAnalysisUnitRunnerManager`.

The JVM forward-analysis hooks record a source `(statement, rule, action)` only
after the evaluator produced an output fact:

- `JIRMethodCallTaintUtil#applySourceAction`: method-call sources, after
  exit-to-return mapping succeeds.
- `JIRSequentTaintUtil#applySourceAction`: method-exit sources.
- `JIRMethodStartFlowFunction#propagateZero`: entry-point sources.
- `JIRMethodSequentFlowFunction#applyUnconditionalSources`: static-field
  sources.

Trace-recomputation calls are excluded. Confirmed shallow vulnerabilities add
their sink rules with an empty action set.

After normal trace-based actionable-rule search, `TaintAnalyzer` compares exact
atoms:

```text
(statement, rule, action?)
```

`action=null` denotes a sink. It logs counts plus every forward-only and
trace-only atom. A trace-only atom is a safety blocker: it proves that the
forward recorder missed something required by the current implementation.
The report emits both raw trace contents and the effective JVM-provider
subset. Raw pass-through and cleaner actions are excluded from the effective
comparison because `SelectedTaintRulesProvider` delegates those categories.

## Semantics

### Cheap global selection

The experimental map is deliberately a global over-approximation:

```text
all source actions that emitted a shallow-forward fact
    union
all sink rules of confirmed shallow vulnerabilities
```

It may include source actions whose facts never reach a confirmed sink, are
later cleaned, or are used only in another calling context. This can increase
the full-scan workload, but it cannot create a vulnerability by itself: the
full forward analysis must still establish source-to-sink reachability.

If every source-producing operation is instrumented, the expected relation is:

```text
effective, forward-representable trace-selected atoms
    ⊆ forward-derived atoms
```

The qualification matters. Trace recomputation currently admits pass-through
actions that the selected provider delegates anyway, and it can reconstruct
facts on primitive values that forward analysis intentionally refuses to
store. Neither category is an actionable forward-source requirement.

### What a flat global set cannot preserve

The current trace search preserves source/sink correlation and rejects a
vulnerability when no valid nested summary trace can be resolved. A global
forward set does neither. Therefore it is suitable as:

1. a safe full-scan rule over-selection mechanism, and
2. a way to remove actionable-rule trace resolution from the critical path,

but not as a replacement for final vulnerability trace validation.

Summary subsumption and field generalization make a flat provenance set even
less precise. If provenance is attached directly to a generalized summary
edge, provenance from a narrower removed edge would be incorrectly available
to every application of the generalized edge.

Persisted summaries also create a completeness requirement. On a cache hit,
`MethodAnalyzer#loadSummariesFromRunner` installs serialized edges without
executing the source evaluators that the experimental hooks observe. A source
action represented only by such a summary can therefore be missing from the
forward-derived set.

Before production use, persisted summaries must carry conservative
method-level source provenance:

```text
Map<statement, Map<source rule, Set<successful action>>>
```

The provenance is serialized beside the summary, unioned when summaries are
loaded or applied, and versioned with the summary format. An old summary
without provenance must be invalidated/recomputed (or conservatively fall back
to trace-based rule selection). Method-level union is sufficient for the
global over-selection design. It is not sufficient for the exact
per-vulnerability design below.

## Exact per-vulnerability design, if global selection is too broad

Record a compact proof dependency DAG during the shallow forward analysis.
Each canonical forward edge points to proof nodes:

```text
LocalAction(statement, rule, action, predecessor)
Flow(predecessor)
SummaryApply(callerPredecessor, summaryProof)
Join(predecessors)
```

At a sink, store the proof-root identities together with the vulnerability
fact group. After confirmation, traverse only those roots and union their
`LocalAction` tokens.

Required invariants:

- When a known edge gains a new proof predecessor, enqueue the proof update
  even though the fact itself is not new.
- Summary storage keeps guarded proof alternatives. Subsumption may redirect a
  removed summary edge to a surviving edge, but must not flatten the removed
  edge's provenance into an unconditional token set.
- An N-dimensional edge records dependencies on all participating initial
  facts.
- Conditional rule tokens are added only after the condition succeeds and the
  action emits a fact.
- Sink proof roots retain the exact trigger position and fact group.

This design preserves correlation without materializing `FullTrace`, but it is
substantially more invasive than global selection and can have edge-by-proof
growth. It should be implemented only if measurements show that the global
over-selection makes the full scan too expensive.

## Conductor experiment

The gated experiment was run with `--ifds-ap-mode BaseOnlyField` on the
Conductor project and its project-specific rules/approximations.

Raw trace contents:

```text
forward=6616, trace=2270, common=1039,
forward-only=5577, trace-only=1231
```

Of the 1231 raw trace-only atoms, 1229 are pass-through actions. They are not a
safety blocker because the selected provider always delegates pass-through
rules.

The effective provider-selected comparison is:

```text
forward=6616, trace=1041, common=1039,
forward-only=5577, trace-only=2
```

The two trace-only source atoms are:

1. `java.lang.String#getBytes()` assigning a mark to `Result.Element` (`byte`).
2. `WorkflowModel#getPriority()` assigning a mark to `Result` (`int`).

Both are primitive/primitive-element results that the forward analysis
intentionally drops. They can appear in trace recomputation, but cannot
contribute a stored forward fact under the strict primitive policy. Therefore
there are zero non-primitive effective trace-only atoms.

Timing from this run:

```text
prescan                 28.08s
shallow forward         27.01s
actionable rule search  43.60s
```

The global forward map is available immediately after shallow scan; replacing
rule search would remove the observed 43.60-second phase. Its 5577 additional
atoms mean the full-scan cost must be measured before rollout. The current
trace-selected full scan in this run took 17.58s; shallow time (27.01s) is a
conservative first-order upper-bound signal, not a substitute for a direct
forward-selected full-scan measurement.

The experiment is observational: it still runs trace-based actionable-rule
search and still feeds the trace-selected map to the full scan. It proves the
set difference, but it does not yet prove the end-to-end time or memory of a
forward-selected full scan.

## Bypass modes

There are two distinct deployment choices:

1. **Bypass actionable-rule trace search only.** Keep shallow vulnerability
   confirmation, union successful forward source actions with the confirmed
   sink rules, and feed that map to the full scan. This removes the expensive
   `TraceActionSearcher` phase while retaining the existing shallow
   confirmation gate.
2. **Bypass all shallow backward work.** Union successful source actions with
   sink rules from raw shallow vulnerabilities. This is more conservative and
   avoids shallow confirmation, but it can select additional sinks and further
   increase full-scan work. Final vulnerability confirmation and trace
   generation remain mandatory correctness gates.

Mode 1 is the initial rollout target. Mode 2 should be evaluated only after
Mode 1 has matching final findings and acceptable full-scan cost.

## Mitigation rollout

1. Add persisted-summary provenance and tests for generate/store/load/apply.
2. Run the gated comparison on Conductor and representative unit/querylang
   suites. Require zero non-primitive effective trace-only source atoms.
   Sink-only differences caused by trace-search failures must be reported
   separately.
3. Add an analyzer option for bypass Mode 1; keep final full-scan
   confirmation and trace validation.
4. Compare final finding identities, full-scan time, peak memory, and status
   against trace selection. The intended improvement is elimination of the
   actionable-rule trace-resolution phase.
5. Add the equivalent successful-source hooks and summary provenance for Go
   before enabling the mechanism in the common staged analyzer for Go.
6. Evaluate bypass Mode 2 separately.
7. If global over-selection is too large, implement the proof-DAG refinement
   rather than reintroducing eager `FullTrace` materialization.

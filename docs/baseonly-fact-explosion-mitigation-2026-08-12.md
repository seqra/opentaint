# BaseOnly fact-explosion mitigation

Date: 2026-08-12

## Evidence

The dominant Conductor method is generated protobuf code:

```text
WorkflowTaskPb.WorkflowTask.Builder.mergeFrom(WorkflowTask)
```

Its repeated pattern is a sequence of guarded field copies:

```java
if (!other.getName().isEmpty()) {
    name_ = other.name_;
    bitField0_ |= 0x00000001;
    onChanged();
}
```

Different input fields produce different exact initial facts, but converge on the same current
fact at many statements. The production diagnostic measured:

```text
220,417 (statement, final) groups
1,033,149 exact initial supports
maximum 15 supports in one group
```

The supports split as follows:

| next operation | groups | exact supports | share of supports |
|---|---:|---:|---:|
| dead-local rejection | 4,870 | 18,211 | 1.8% |
| call | 93,326 | 438,256 | 42.4% |
| sequential | 122,221 | 576,682 | 55.8% |

Early local-liveness filtering is therefore sound but not the main mitigation. The dominant cost
is repeated transfer work for alternative exact premises with the same conclusion.

## Semantics

An F2F path edge is:

```text
exact initial premise -> (statement, final fact)
```

Several initials for the same conclusion are a **disjunction of provenance alternatives**. They
must not be converted to an ND edge: ND initials are a conjunction. They must also not be removed
using access-path coverage. A broader and a narrower initial can produce different correlated
method summaries and different trace witnesses later.

The safe optimization is therefore factorization, not semantic subsumption:

```text
(statement, final fact) -> exact initial support set
```

The analysis performs conclusion-only work once and retains every exact support for storage,
summary construction, subscriptions, and trace resolution.

## Implemented first stage

1. The BaseOnly F2F worklist is keyed by `(statement, final fact)` and carries a compact exact
   support set.
2. Transparent CFG closure and ordinary non-exit sequential transfer are computed once per
   conclusion.
3. Changed outputs are inserted into the exact F2F relation through a batch callback API; no
   `Edge.FactToFact` object is required per premise at this stage.
4. Unchanged-boundary deduplication is also factorized by conclusion.
5. CFG exits, initial-sensitive transfers, and calls remain explicit barriers.
6. The first call specialization handles only the provably identical case where
   `factIsRelevantToMethodCall` is false. Every premise then has exactly the `Unchanged` result.

This preserves the exact relation queried by `MethodAnalyzerEdgeSearcher` and
`MethodTraceResolver`.

On Conductor's hot `WorkflowTask.Builder.mergeFrom(WorkflowTask)` method, this specialization
changed the deterministic work counters from:

```text
601,216 analyzer steps
```

to:

```text
357,798 analyzer steps
59,737 shared irrelevant-call transfers for 273,764 exact supports
```

That is a 40.5% reduction in hot-method steps. Both scans reported the same six semantic
findings (rule, sink fingerprint, and source/sink fingerprint). Two trace-only fingerprints
changed because trace sampling is not canonical across runs.

The worklist grouping is intentionally transient: exact premises discovered in different
fixed-point rounds are processed separately. A regression sample therefore uses a relevant
`passthrough(selected)` call as a synchronization boundary before an irrelevant call. This is
the same generated-code shape observed in Conductor, where repeated getters and `onChanged()`
calls synchronize alternative field premises.

## Remaining call mitigation

The next call plan must split final-dependent planning from premise-dependent instantiation.

Safe initial eligibility:

1. BaseOnly F2F group only.
2. Sink and source rule lists are empty.
3. Every mapped caller fact has no cleaner rules.
4. Call mapping is computed once from the final fact.
5. Each resulting call-to-start/call-to-return template is instantiated for every exact initial
   support. Exact subscriptions and caller edges are retained.

Fallback to scalar processing is required for source assumptions, any-field sink resolution,
cleaners, side-effect requirements, unresolved pass rules, and lambdas until each has an explicit
support-parametric representation. Passing the support set as `initialFacts` is forbidden because
that changes an OR of alternatives into an ND conjunction.

## Storage representation

The current conclusion index shares the conclusion object but still stores exact supports in
object sets. The production representation should use a statement-local bidirectional Boolean
relation:

```text
initial access ID -> adaptive set of final IDs
final access ID   -> adaptive set of initial IDs
```

An adaptive set uses singleton/few/bitmap forms. This preserves every exact cell while replacing
two hash-set entries per relation cell with dense integer membership. Equal immutable support
bitmaps may later be hash-consed as support classes; mutable bitmaps must not be shared.

## Mitigation stages

The measured profile supports this order:

1. Retain conclusion-keyed F2F scheduling and the narrow irrelevant-call specialization. This
   removes repeated transfer computation without changing the path-edge relation.
2. Add a support-parametric call plan for rule-free and cleaner-free calls. Compute mapping and
   resolved-call relevance once from the final fact, then instantiate exact subscriptions and
   call-to-return edges for every initial support. Fall back before any initial-sensitive action.
3. Replace object support sets with the bidirectional integer relation above. Forward work needs
   `final -> initials`; trace membership also needs `initial -> finals`, so neither direction may
   be discarded.
4. Add early local-liveness rejection at insertion. It is safe but secondary: only 1.8% of the
   hot Conductor method's exact supports were rejected at processing time.
5. Treat class-static context multiplication separately using the transitive static-footprint
   design. It is the dominant ThingsBoard pattern and cannot be solved by merging F2F premises.

Do not apply access-path subsumption to the initial support set. The supports are disjunctive
provenance alternatives, and a wider access path does not preserve the correlation between one
method premise and its conclusion.

## Validation obligations

- Scalar and batch insertion publish identical deltas for Tree, Automata, Cactus, and BaseOnly.
- Exclusion growth may re-emit several finals; batch propagation must regroup the complete delta.
- A branch/join sample must retain all exact field premises and a complete source-to-sink trace.
- Conditional source, sink-any-field, cleaner, unresolved pass, constructor, and lambda samples
  must exercise scalar fallback.
- Conductor must retain the same final rule/fingerprint set.
- Wall-clock comparisons must use repeated isolated runs; operation and support counts are the
  primary deterministic signal on a shared machine.

## Current validation status

- The BaseOnly storage suite passes (410 tests).
- The branch/join exact-support test and the synchronized irrelevant-call test pass.
- Go querylang passes (761 tests).
- Java querylang has one `PositiveNdRule` failure. The same failure reproduces in a clean detached
  worktree containing only the user's staged soft-reset state, before this mitigation is applied;
  it is therefore not introduced by conclusion grouping. Disabling staged ND-result
  deduplication alone does not fix it; the loss is in the staged return-summary path and remains a
  separate investigation.
- The existing field-generalization test expects one edge but observes 381 because field
  generalization is disabled by default in the current staged state.

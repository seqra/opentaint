# BaseOnly trace-resolution fuzz evidence

## Result

Six nested-factory variants were investigated and all had the same trace-side root cause. The minimal `nestedFactory` variant is retained as the regression test. It is not a forward-analysis miss:

- Tree creates one pre-trace vulnerability and resolves its path.
- BaseOnlyField also creates one pre-trace vulnerability.
- BaseOnlyField then logs `Trace has no resolved paths` and filters that vulnerability.

The incorrect operation is the `fact.hasAp` branch of `BaseOnlyAccessOps.splitDelta`. When an abstract caller fact equals an abstract mapped summary final, it always returns `BaseOnlyEmptyInitialDelta`. `MethodTraceResolver.resolveCallPassSummary` concatenates that empty delta onto the mapped summary initial. If the summary moves a nested value from a constructor argument into a receiver field, this changes `var(1).value.*` into the bare fact `var(1)`. The reconstructed fact is not present in the recorded forward edge, so trace resolution stops.

## Exact operation evidence

The retained case reaches the synthetic `Envelope` constructor call with this BaseOnly state:

```text
statement       = %0.<init>(%1, null)
callerFact      = var(0).box.*/{}
summary initial = arg(0)/{}
summary final   = <this>.box.*/{}
mapped final    = var(0).box.*/{}
splitDelta      = [(var(0).box.*/{}, BaseOnlyEmptyInitialDelta)]
mapped initial  = var(1)/{}
result          = var(1)/{}
stored edge fact= var(1).value.*/{}
contains        = false
```

The corresponding Tree operation retains the suffix:

```text
callerFact      = var(0).box.value.*/{}
summary final   = <this>.box/*
splitDelta      = [(var(0).box.*/{}, Delta(.value))]
mapped initial  = var(1).*/{}
result          = var(1).value.*/{}
```

The BaseOnly result is unsound for trace reconstruction. The abstract suffix in `box.*` denotes a descendant that has not necessarily been consumed by the summary. Returning an empty residual and substituting the bare argument asserts that no descendant remains. The expected result must remain compatible with the recorded `var(1).value.*` forward fact. An implementation may recover that compatible representative from the stored forward edges, or propagate a sound abstract residual and refine it against those edges, but it must not produce bare `var(1)`.

The trace builder finally reports no applicable action at `%1.<init>(value, null)` (`Box.<init>`). The fact was already corrupted at the preceding `Envelope.<init>` summary application: the resolver requests bare `var(1)`, while its forward edge store contains `var(1).value.*`.

## Incorrect code path

The operation is in `BaseOnlyAccessOps.splitDelta`:

```kotlin
if (fact.hasAp) {
    if (!containsAccess(pattern, fact)) return emptyList()
    return listOf(pattern to BaseOnlyEmptyInitialDelta)
}
```

It is invoked by `MethodTraceResolver.resolveCallPassSummary` as:

```kotlin
val mappedSummaryFact = summaryEdge.factAp.rebase(callerFact.base)
val deltas = callerFact.splitDelta(mappedSummaryFact)
// ...
val precondition = mappedSummaryInitialFact.concat(delta)
```

The branch conflates “the abstract caller is covered by the summary final” with “the summary final consumed the entire unknown descendant suffix.” These are not equivalent when the summary changes the base from a receiver field to a constructor argument.

## Reproduction

```bash
cd core
./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.JavaDataFlowReachabilityTest.base-only flow - trace resolves through nested factory result' \
  -x :opentaint-ir:go:buildGoServer \
  --no-daemon --max-workers=1
```

Observed for the BaseOnly run:

```text
Total vulnerabilities: 1
Trace has no resolved paths
Filter out 1 vulnerabilities without traces
```

Temporary probes were placed around `resolveCallPassSummary`, `containsEntryEdge`, and the trace-builder early returns to collect the fact tuples above. The probes were removed after collection.

# BaseOnly trace-resolution fuzz evidence

## Result

All six nested-factory cases have the same trace-side root cause. They are not forward-analysis misses:

- Tree creates one pre-trace vulnerability and resolves one path for every case.
- BaseOnlyField also creates one pre-trace vulnerability for every case.
- BaseOnlyField then logs `Trace has no resolved paths` and filters that vulnerability.

The incorrect operation is the `fact.hasAp` branch of `BaseOnlyAccessOps.splitDelta`. When an abstract caller fact equals an abstract mapped summary final, it always returns `BaseOnlyEmptyInitialDelta`. `MethodTraceResolver.resolveCallPassSummary` concatenates that empty delta onto the mapped summary initial. If the summary moves a nested value from a constructor argument into a receiver field, this changes a fact such as `var(1).value.*` or `var(1).box.*` into the bare fact `var(1)`. The reconstructed fact is not present in the recorded forward edge, so trace resolution stops.

## Exact operation evidence

The two-level cases reach the synthetic `Envelope` constructor call with this BaseOnly state:

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

The three-level cases fail one wrapper earlier, at the synthetic `Outer` constructor call:

```text
statement       = %0.<init>(%1, null)
callerFact      = var(0).envelope.*/{}
summary initial = arg(0)/{}
summary final   = <this>.envelope.*/{}
mapped final    = var(0).envelope.*/{}
splitDelta      = [(var(0).envelope.*/{}, BaseOnlyEmptyInitialDelta)]
mapped initial  = var(1)/{}
result          = var(1)/{}
stored edge fact= var(1).box.*/{}
contains        = false
```

Tree again retains the structural remainder:

```text
callerFact      = var(0).envelope.box.value.*/{}
summary final   = <this>.envelope/*
splitDelta      = [(var(0).envelope.*/{}, Delta(.box.value))]
mapped initial  = var(1).*/{}
result          = var(1).box.value.*/{}
```

The BaseOnly result is unsound for trace reconstruction. The abstract suffix in `box.*` or `envelope.*` denotes a descendant that has not necessarily been consumed by the summary. Returning an empty residual and substituting the bare argument asserts that no descendant remains. The expected result must remain compatible with the corresponding recorded forward fact: `var(1).value.*` in the two-level flows and `var(1).box.*` in the three-level flows. An implementation may recover that compatible representative from the stored forward edges, or propagate a sound abstract residual and refine it against those edges, but it must not produce bare `var(1)`.

## Per-case evidence

| fuzz case | faulty summary application | fact before | incorrect reconstructed fact | recorded forward fact | first predecessor that cannot be crossed |
|---|---|---|---|---|---|
| `nestedFactory` | `envelope`: `new Envelope(new Box(value))`, `Envelope.<init>` | `var(0).box.*` | `var(1)` | `var(1).value.*` | `%1.<init>(value, null)` (`Box.<init>`) |
| `nestedFactoryViaBoxFactory` | `envelopeViaBox`: `new Envelope(box(value))`, `Envelope.<init>` | `var(0).box.*` | `var(1)` | `var(1).value.*` | `%1 = BaseOnlyTraceResolutionFuzzSample.box(value)` |
| `delegatedNestedFactory` | delegated call reaches `envelope`, then `Envelope.<init>` | `var(0).box.*` | `var(1)` | `var(1).value.*` | `%1.<init>(value, null)` (`Box.<init>`) |
| `threeLevelFactory` | `outer`: `new Outer(new Envelope(...))`, `Outer.<init>` | `var(0).envelope.*` | `var(1)` | `var(1).box.*` | `%1.<init>(%2, null)` (`Envelope.<init>`) |
| `threeLevelFactoryViaEnvelopeFactory` | `outerViaEnvelope`: `new Outer(envelope(value))`, `Outer.<init>` | `var(0).envelope.*` | `var(1)` | `var(1).box.*` | `%1 = BaseOnlyTraceResolutionFuzzSample.envelope(value)` |
| `delegatedThreeLevelFactory` | delegated call reaches `outer`, then `Outer.<init>` | `var(0).envelope.*` | `var(1)` | `var(1).box.*` | `%1.<init>(%2, null)` (`Envelope.<init>`) |

The “first predecessor” column is where the trace builder finally reports that it has no applicable action. The fact was already corrupted at the preceding wrapper-constructor summary application: the resolver requests bare `var(1)`, while its forward edge store contains the field-qualified fact shown in the previous column.

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
  --tests 'org.opentaint.jvm.sast.dataflow.JavaDataFlowReachabilityTest.base-only flow - traces resolve through nested factory results*' \
  -x :opentaint-ir:go:buildGoServer \
  --no-daemon --max-workers=1
```

Observed for all six BaseOnly runs:

```text
Total vulnerabilities: 1
Trace has no resolved paths
Filter out 1 vulnerabilities without traces
```

Temporary probes were placed around `resolveCallPassSummary`, `containsEntryEdge`, and the trace-builder early returns to collect the fact tuples above. The probes were removed after collection.

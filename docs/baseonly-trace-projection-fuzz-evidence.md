# BaseOnly trace-projection fuzz evidence

## Result

All four `BaseOnlyTraceProjectionFuzzTest` cases had the same trace-resolution root cause. They were not forward-analysis misses. Before the fix, every Tree and BaseOnly run created one vulnerability in forward analysis, but BaseOnly reached trace generation and then rejected it:

```text
Total vulnerabilities: 1
Filter out 1 vulnerabilities without traces
```

The final loss occurs while matching the whole-object `AnyField` source at the `source()` call. Backward BaseOnly resolution reaches the call with:

```text
fact     = ret![trace-projection-taint].$/*
position = ret.[any]
mark     = ![trace-projection-taint]
```

`/*` is the rendered universe exclusion set; the access itself is the mark followed by the final accessor.

The source precondition evaluator calls `InitialFactReader.containsPositionWithTaintMark`, which reads `[any]`, the mark, and the final accessor. The BaseOnly access API gives inconsistent answers for the mark-only fact:

```text
startsWithAccessor(AnyAccessor) = true
readAccessor(AnyAccessor)       = ret![trace-projection-taint].$/*
getStartAccessors()             = [![trace-projection-taint]]
contains(ret.[any] + mark)      = false
```

`BaseOnlyAccessOps.headRead` explicitly treats every structural accessor, including `AnyAccessor`, as a self-loop (`KEEP`) before a semantic mark. However, `BaseOnlyApManager.startAccessors` returns only `headOrNull`, which is the mark. The generic any-accessor reader enumerates `getStartAccessors()`. It therefore consumes the mark as the field and cannot match the same mark afterward.

Consequently, the source call precondition contains only the body edge:

```text
CallToStart(callerFact=ret![trace-projection-taint].$, startFactBase=ret)
```

It does not contain the required `CallToReturnTaintRule(Source(... AnyFieldAccessor ...))`. The empty `source()` body has no source summary, so no `SourceStartEntry` is created and the interprocedural trace graph has no source-connected path.

Tree reaches the same call with a concrete structural path such as:

```text
ret.envelope.box.value![trace-projection-taint].$.*/*
```

Its first start accessor is `envelope`, so `[any]` consumes a real field and the source rule matches.

## Incorrect BaseOnly operation

The primary defect is the disagreement between these two BaseOnly operations:

```kotlin
// BaseOnlyAccessOps.headRead
access.hasSemanticMark -> when {
    structural(idx) -> HeadRead.KEEP
    idx == access.suffixIdx -> HeadRead.TAIL
    else -> HeadRead.NONE
}

// BaseOnlyAccessView.startAccessors
val head = access.headOrNull ?: return emptySet()
return setOf(interner.accessor(head)!!)
```

For a semantic-mark-only fact, the first operation says a virtual structural edge exists, while the second hides that edge from algorithms that enumerate possible starts. `readPositionWithAnyAccessorSplit` uses enumeration, not `startsWithAccessor`, so the hidden edge rejects the source.

Expected behavior: the BaseOnly accessor view must expose a structural/`AnyAccessor` self-loop whenever `headRead` permits structural `KEEP`, or the any-accessor reader must otherwise honor that self-loop. It must be possible to read `[any]` and then the semantic mark from this overapproximated fact.

### Fix and validation

`BaseOnlyApManager.startAccessors` now returns `AnyAccessor` in addition to the concrete head when the suffix is a taint-mark accessor:

```kotlin
return if (access.hasSemanticMark && access.suffixIdx.isTaintMarkAccessor()) {
    setOf(AnyAccessor, concreteHead)
} else {
    setOf(concreteHead)
}
```

The taint-mark check is intentionally narrower than `hasSemanticMark`, which also includes type-info suffixes. Type-info facts retain their existing start-accessor behavior. With no other behavioral change, all four differential tests pass:

```text
projectOneLevel      PASSED
projectThreeLevels   PASSED
relayThenProject     PASSED
mutateThenProject    PASSED
BUILD SUCCESSFUL
```

Disabling normalized summary aliases did not change any of the four failures, so `normalizeSummaryInitialAccess` is not their cause.

## Per-test evidence

### `projectOneLevel`

Source:

```java
Outer value = source();
Envelope result = projectEnvelope(value);
sink(result.box.value);
```

BaseOnly walks backward from the sink successfully:

```text
sink(%5)          : %5![mark].$
%5 = %4.value     : %4.value![mark].$
%4 = result.box   : result.box![mark].$
```

At `result = projectEnvelope(value)`, BaseOnly applies:

```text
caller fact          = result.box![mark].$
summary              = arg(0).* -> ret.*
mapped summary final = result.*
splitDelta actual    = matched result.*, delta ![mark].$
mapped initial       = value.*
reconstructed input  = value![mark].$
```

This is an earlier precision divergence: `BaseOnlyAccessOps.splitConcreteInitial`, in its suffix-AP branch, removes both structural slots and retains only the semantic suffix. It drops `.box` even though that field is representable. Tree retains `.box.value![mark].$` and reconstructs `value.envelope.box.value![mark].$`.

The reconstructed BaseOnly fact is still present in the recorded forward edges, so `containsEntryEdge` accepts it. The trace finally terminates at `value = source()` because the mark-only fact fails the inconsistent `[any]` source match described above.

### `projectThreeLevels`

Source:

```java
Outer value = source();
sink(projectToken(value));
```

Backward BaseOnly state at `%2 = projectToken(value)`:

```text
caller fact          = %2![mark].$
summary              = arg(0).* -> ret.*
mapped summary final = %2.*
splitDelta           = matched %2.*, delta ![mark].$
mapped initial       = value.*
reconstructed input  = value![mark].$
```

There is no caller-side field to preserve because `projectToken` returns the final token directly. Tree can retain the full relational summary `arg(0).envelope.box.value.* -> ret.*`; BaseOnly's one-field abstraction has the coarser `arg(0).* -> ret.*` summary. Initial-fact diagnostics show the abstraction input and output:

```text
input   = arg(0)![mark].$
output  = arg(0).*
```

The coarse fact is a valid BaseOnly overapproximation, so trace resolution must be able to connect it to an `AnyField` source. Instead, `value = source()` rejects it because `getStartAccessors()` omits the virtual `AnyAccessor` edge. No source action is created.

### `relayThenProject`

Source:

```java
Outer value = relayOuter(source());
Envelope result = relayEnvelope(projectEnvelope(value));
sink(result.box.value);
```

The first backward precision loss is at `result = relayEnvelope(%3)`:

```text
caller fact          = result.box![mark].$
relay summary        = arg(0).* -> ret.*
splitDelta actual    = matched result.*, delta ![mark].$
reconstructed input  = %3![mark].$
```

`.box` is discarded by the same `splitConcreteInitial` suffix-AP branch as in `projectOneLevel`. The mark-only fact then crosses `projectEnvelope` and `relayOuter`; all per-statement forward-edge containment checks succeed. At `%0 = source()`, source matching observes:

```text
fact                 = ret![mark].$
startsWith([any])    = true
read([any])          = same fact
getStartAccessors()  = [mark]
source match         = false
```

Thus the relays and dispatch are resolved; the terminal rejection is the BaseOnly accessor-enumeration defect.

### `mutateThenProject`

Source:

```java
Outer value = source();
touchOuter(value);
touchEnvelope(value.envelope);
touchBox(value.envelope.box);
sink(projectToken(value));
```

The `projectToken` reversal has the same state as `projectThreeLevels`:

```text
caller fact          = result![mark].$
summary              = arg(0).* -> ret.*
splitDelta           = ![mark].$
reconstructed input  = value![mark].$
```

Backward resolution successfully applies the `touchBox`, `touchEnvelope`, and `touchOuter` summaries and finds matching forward facts at every field read and call. The unrelated writes do not drop the fact. The trace reaches `value = source()` twice through valid alias/side-effect alternatives; both attempts have the mark-only fact and both reject the `AnyField` source for the same accessor-enumeration inconsistency.

## Common failure chain

```text
forward BaseOnly analysis reaches sink and records vulnerability
  -> backward summaries reconstruct an overapproximated mark-only fact
  -> containsEntryEdge accepts the fact at every caller statement
  -> source precondition asks for [any] then mark
  -> BaseOnly startsWith/read say [any] is a valid self-loop
  -> BaseOnly getStartAccessors omits that self-loop
  -> generic AnyAccessor traversal consumes the mark as the field
  -> source rule is absent from call preconditions
  -> empty source body supplies no source summary
  -> trace graph has no source-connected path
  -> vulnerability is filtered out
```

## Reproduction

```bash
cd core
./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.BaseOnlyTraceProjectionFuzzTest' \
  -x :opentaint-ir:go:buildGoServer \
  --no-daemon --max-workers=1 --console=plain
```

Expected current result: all four dynamic tests pass in both Tree and BaseOnly modes.

Temporary probes were placed around call-summary reversal, `containsEntryEdge`, initial-fact abstraction, source-action precondition matching, and trace-path expansion. They were removed after collection. Diagnostic logs from this investigation are retained in `/tmp/baseonly-trace-projection-*.log` in the current workspace.

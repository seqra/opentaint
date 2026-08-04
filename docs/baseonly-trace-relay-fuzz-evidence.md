# BaseOnly trace-relay fuzz evidence

## Result

All six original `BaseOnlyTraceResolutionFuzzTest` failures had the same root operation. They were not forward-analysis misses: every BaseOnly run reported one vulnerability before trace generation. Backward trace resolution lost a concrete field refinement while inverting a relay method's F2F summary.

The failing operation is `BaseOnlyAccessOps.splitDelta`:

```kotlin
if (fact.hasAp) {
    if (!containsAccess(pattern, fact)) return emptyList()
    return listOf(pattern to BaseOnlyEmptyInitialDelta)
}
```

For these flows, the operands are logically:

```text
fact    = <concrete-field>.*       (-1, field, -2)
pattern = <field-*>                (-1,    -2, -1)
actual  = (<field-*>, empty delta)
```

`containsAccess(pattern, fact)` correctly says that the field abstraction covers the concrete field. The following unconditional empty delta is incorrect: it drops the concrete field refinement. The corresponding Tree operation retains the suffix as a non-empty delta and reconstructs the original predecessor fact.

The expected BaseOnly result is a node delta carrying `<concrete-field>.*`, so concatenating it with the mapped summary initial reconstructs `<concrete-field>.*`. This is also consistent with `splitConcreteInitial`'s existing AP-at-field behavior; that helper currently rejects the case only because the input itself has a suffix abstraction.

`BaseOnlyApManager.renderAccess` does not render an `ABSTRACT_MARK` in the field slot. Consequently the raw field abstraction `(-1, -2, -1)` appears as a visually bare `var/{}` in the diagnostic excerpts below. It is not an empty access.

## Implemented fix

When the summary pattern has field-AP and the backward fact has a concrete field followed by suffix-AP, `splitDelta` now returns a `BaseOnlyNodeInitialDelta` containing that concrete field and suffix abstraction:

```text
before: splitDelta(field.*, <field-*>) = (<field-*>, ε)
after:  splitDelta(field.*, <field-*>) = (<field-*>, Δfield.*)
```

The change is deliberately limited to this representable refinement. Other AP-slot relationships retain their existing behavior. The exhaustive mode-1 split table changes exactly nine field/element cases from empty to structural deltas; mode 0 is unchanged.

## Phase evidence

Before the fix, for each of the six methods the Tree run succeeded and the BaseOnly run emitted:

```text
Total vulnerabilities: 1
Trace has no resolved paths
Filter out 1 vulnerabilities without traces
```

Thus the sink and vulnerability exist in forward analysis; the finding is rejected only after backward trace resolution fails.

Before the fix, the complete JVM `*FuzzTest` run executed 107 tests: exactly these six failed and the other 101 passed. After the fix, all 107 pass, including all six Tree and BaseOnly assertions in `BaseOnlyTraceResolutionFuzzTest`.

## Per-test evidence

### `returnThroughIdentity`

Source statement: `return identity(envelope)` in `identityFactory`.

Tree inversion at `%3 = identity(envelope)`:

```text
caller fact          = %3.box.value.*
relay summary        = arg(0).* -> ret.*
splitDelta           = matched %3.*, delta .box.value
reconstructed input  = %2.box.value.*
stored fact          = %2.box.value.*
containsEntryEdge    = true
```

BaseOnly inversion:

```text
caller fact          = %3.box.*                 (-1, box, -2)
relay summary        = arg(0).<field-*> -> ret.<field-*>
splitDelta actual    = matched %3.<field-*>, BaseOnlyEmptyInitialDelta
reconstructed input  = %2.<field-*>             (-1, -2, -1)
stored fact          = %2.box.*                  (-1, box, -2)
containsEntryEdge    = false
```

The trace stops while moving from `%3 = identity(envelope)` to the preceding `envelope.<init>(%1)`. The lost refinement is `.box.*`.

### `returnThroughDoubleIdentity`

Source statement: `return identity(identity(envelope))` in `doubleIdentityFactory`.

Tree inverts the outer identity with a `.box.value` delta and produces `%3.box.value.*`, which matches the fact stored after the inner identity call.

BaseOnly fails at the outer identity, `%4 = identity(%3)`:

```text
caller fact          = %4.box.*
relay summary        = arg(0).<field-*> -> ret.<field-*>
splitDelta actual    = matched %4.<field-*>, BaseOnlyEmptyInitialDelta
reconstructed input  = %3.<field-*>
stored fact          = %3.box.*
containsEntryEdge    = false
```

The resolver therefore never reaches the inner identity. The lost refinement is `.box.*`.

### `returnThroughInstanceIdentity`

Source statement: `return envelope.self()` in `instanceIdentityFactory`.

Tree inversion of `%3 = envelope.self()` uses the `<this>.* -> ret.*` summary, retains delta `.box.value`, reconstructs `%2.box.value.*`, and matches the stored fact.

BaseOnly inversion:

```text
caller fact          = %3.box.*
relay summary        = <this>.<field-*> -> ret.<field-*>
splitDelta actual    = matched %3.<field-*>, BaseOnlyEmptyInitialDelta
reconstructed input  = %2.<field-*>
stored fact          = %2.box.*
containsEntryEdge    = false
```

The trace stops between `%3 = envelope.self()` and `envelope.<init>(%1)`. The static/instance calling convention changes the summary base but not the incorrect operation.

### `returnThroughInterfaceIdentity`

Source statement: `return relay.relay(envelope)` in `interfaceIdentityFactory`.

Tree resolves the implementation summary, retains `.box.value`, and carries `%2.box.value.*` backward across the relay allocation to the `Envelope` constructor.

BaseOnly inversion of `%5 = relay.relay(envelope)` produces:

```text
caller fact          = %5.box.*
relay summary        = arg(0).<field-*> -> ret.<field-*>
splitDelta actual    = matched %5.<field-*>, BaseOnlyEmptyInitialDelta
reconstructed input  = %2.<field-*>
```

That fact remains unchanged across `relay.<init>` and `relay = new EnvelopeRelayImpl`. At the latter statement:

```text
trace query          = %2.<field-*>
stored fact          = %2.box.*
containsEntryEdge    = false
```

The trace stops before reaching `envelope.<init>(%1)`. Dynamic dispatch is resolved successfully; the failure is the same lost `.box.*` delta.

### `returnThroughBranchIdentity`

Source statement: `return choose(envelope, new Envelope(new Box()))` in `branchIdentityFactory`.

Tree selects the first-argument summary of `choose`, retains `.box.value`, and reconstructs `%2.box.value.*`. The rejection of the second-argument branch inside `choose` is expected and is not the failure: the tainted first branch has a valid Tree trace.

BaseOnly inversion of `%5 = choose(envelope, %3)` produces:

```text
caller fact          = %5.box.*
chosen summary       = arg(0).<field-*> -> ret.<field-*>
splitDelta actual    = matched %5.<field-*>, BaseOnlyEmptyInitialDelta
reconstructed input  = %2.<field-*>
```

The reconstructed fact crosses the untainted second-argument allocations unchanged. At `%3 = new Envelope`:

```text
trace query          = %2.<field-*>
stored fact          = %2.box.*
containsEntryEdge    = false
```

The trace stops before the tainted `envelope.<init>(%1)` call. Again, the discarded refinement is `.box.*`.

### `returnOuterThroughIdentity`

Source statement: `return outerIdentity(outer)` in `outerIdentityFactory`.

This case proves the issue is not tied specifically to `Envelope.box`. Tree retains the complete `.envelope.box.value` suffix through the relay:

```text
caller fact          = %4.envelope.box.value.*
relay summary        = arg(0).* -> ret.*
splitDelta           = matched %4.*, delta .envelope.box.value
reconstructed input  = %3.envelope.box.value.*
stored fact          = %3.envelope.box.value.*
containsEntryEdge    = true
```

BaseOnly inversion:

```text
caller fact          = %4.envelope.*             (-1, envelope, -2)
relay summary        = arg(0).<field-*> -> ret.<field-*>
splitDelta actual    = matched %4.<field-*>, BaseOnlyEmptyInitialDelta
reconstructed input  = %3.<field-*>              (-1, -2, -1)
stored fact          = %3.envelope.*              (-1, envelope, -2)
containsEntryEdge    = false
```

The trace stops between `%4 = outerIdentity(outer)` and `outer.<init>(%1)`. The lost BaseOnly refinement is `.envelope.*`.

## Common incorrect operation

All six failures follow the same chain:

```text
relay output concreteField.*
  -> BaseOnlyInitialFactAp.splitDelta(mapped relay final)
  -> BaseOnlyAccessOps.splitDelta sees fact.hasAp
  -> containsAccess(field-AP, concreteField+suffix-AP) = true
  -> returns BaseOnlyEmptyInitialDelta
  -> mapped relay input remains field-AP
  -> containsEntryEdge compares stored concreteField.* against field-AP
  -> BaseOnlyFinalFactAp.contains = false
  -> no predecessor action; trace has no resolved path
```

The caller fact is abstract only at the suffix slot. That does not justify throwing away the already-known concrete field slot. Tree preserves the corresponding suffix, while BaseOnly's early `fact.hasAp` branch prevents the field-leading delta logic from running.

## Reproduction

```bash
cd core
./gradlew :test \
  --tests 'org.opentaint.jvm.sast.dataflow.*FuzzTest' \
  -x :opentaint-ir:go:buildGoServer \
  --no-daemon --max-workers=1 --info
```

Temporary probes were placed around `resolveCallPassSummary`, `containsEntryEdge`, and trace-entry propagation. They printed the caller fact, summary edge, `splitDelta` result, reconstructed predecessor, stored per-statement candidates, and containment result. The probes were removed after collection.

# BaseOnly reference-fuzz forward-miss evidence

## Result

All 101 active differential samples reproduce the same forward-analysis defect:

- Tree creates one pre-trace vulnerability for every sample;
- BaseOnlyField creates zero pre-trace vulnerabilities;
- the source fact reaches the in-project constructor/setter summary;
- `BaseOnlyFinalFactAp.concat` calls `BaseOnlyAccessOps.appendFinal` with a destination prefix ending in `.*` and a field- or element-leading marked delta;
- `appendFinal` returns `null` because `prefix.apSlot != slotOfFirstAccessor(suffix)`;
- summary application consequently emits no destination fact.

This is an AP-algebra engine defect, not a rule, approximation, sink-matching, or trace-resolution failure. Every method on the paths is declared in the three test samples.

## Incorrect operation

For the dominant nested-reference shape, with packed accesses written as `(static, field, suffix)`:

```text
current caller fact = child.payload.!M.$
mapped prefix       = destination.outer.* = (-1, outer, ABSTRACT_MARK)
residual delta      = .payload.!M.$        = (-1, payload, M)

prefix.apSlot                  = 2
slotOfFirstAccessor(delta)     = 1
appendFinal(prefix, delta)     = null
```

Tree concatenates the same operands to `destination.outer.payload.!M.$`. BaseOnly has one field slot, so its least imprecise sound representation is `destination.outer.!M.$`: retain the outer field, absorb the inner field, and preserve the semantic mark. The current `headRead` operation proves this covers the Tree path: reading `outer` exposes `!M.$`, and semantic marks survive every subsequent structural read.

When the prefix is a whole-object `.*` and its field slot is free, the least imprecise result is the field-leading suffix itself. Array element access uses the same structural slot as a field and follows the same rule.

The rejecting code is the equality guard in `BaseOnlyAccessOps.appendFinal`:

```text
if (prefix.apSlot != slotOfFirstAccessor(suffix)) return null
```

The guard incorrectly treats a cross-slot structural refinement as incompatible. In a field-insensitive domain it must collapse the unrepresentable inner structural component and return a covering fact, not discard the flow.

## Evidence inventory

| appendix | cases | evidence |
|---|---:|---|
| [Mutation 000-029](mutation-000-029.md) | 30 | constructors, factories, aliases, and wrapper setters |
| [Mutation 030-059](mutation-030-059.md) | 30 | alternate/keyed/quad constructors and setters |
| [Mutation 060-089 and install/transfer](mutation-060-089-install-transfer.md) | 41 | remaining mutation cases, two installation cases, and nine transfer cases including arrays |

Each appendix identifies the first losing Java statement and records the fact before the statement, mapped summary prefix, residual delta, Tree result, BaseOnly actual result, and sound BaseOnly expected result for every test.

## Direct algebra probe

An independent direct call to the current `BaseOnlyAccessOps.appendFinal` confirmed these results:

```text
field.* + field+mark   current=null  expected=(static, outerField, mark)
whole.* + field+mark   current=null  expected=(static, innerField, mark)
field.* + element+mark current=null  expected=(static, outerField, mark)
whole.* + element+mark current=null  expected=(static, element, mark)
```

Reading each proposed result along its concrete Tree field/element sequence leaves the mark fact, establishing that the expected result is a sound BaseOnly overapproximation.

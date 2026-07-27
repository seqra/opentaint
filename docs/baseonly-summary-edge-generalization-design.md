# BaseOnly F2F summary-edge generalization

## Goal

A field-sensitive method can produce a quadratic family of F2F summaries:

```text
(-1, -2, -1) -> (-1, -2, -1)
(-1,  x, -2) -> (-1, -1, -2)
(-1,  x, -2) -> (-1,  y, -2)
...
```

The end-to-end reproduction in
`BaseOnlySummaryFieldExplosionTest` nondeterministically reads 20 fields and
writes the selected value to 20 fields. Its helper retains:

```text
1        field-abstract identity
20       concrete-field -> abstract-tail edges
20 * 19  off-diagonal concrete-field relocations
--------
401      F2F summaries
```

The desired bounded representation is:

```text
(-1, -1, -2) /{} -> (-1, -1, -2) /{}
```

This is an explicit field-erasing widening. It is not ordinary summary-edge
subsumption.

## Why exact subsumption cannot perform this collapse

An F2F summary is a correlated transformation. Under exact summary semantics,

```text
.* -> .*
```

does not subsume:

```text
.x.* -> .y.*
```

The latter installs the input residual under `y`; the identity edge does not.
`BaseOnlySummaryEdgeOps.subsumes` must therefore remain exact and must not be
weakened for this optimization.

Generalization instead forgets which field was read and which field was
written. Applying the generalized edge produces an abstract final fact that
covers every concrete final field. False-positive paths are an accepted cost
of the widening; losing a forward result is not.

## Field-erasure projection

Generalization is local to one method entry, initial base, and final base.
Those bases are never merged.

The eligible access shapes are:

```text
(static, ABSTRACT_MARK, NO_ACCESSOR)
(static, concreteField, ABSTRACT_MARK)
(static, NO_ACCESSOR, ABSTRACT_MARK)
```

They all project to:

```text
eraseField(access) =
    (access.staticIdx, NO_ACCESSOR, ABSTRACT_MARK)
```

The static slot is preserved. Normal and Value suffix states, semantic marks,
type-information accessors, final accessors, and incompatible static prefixes
must not be merged.

An eligible edge belongs to the group:

```text
GroupKey(
    initialBase,
    finalBase,
    eraseField(initialAccess),
    eraseField(finalAccess),
)
```

Its generalized representative is exactly the two projected accesses from the
group key.

## Generalization trigger

Do not widen a single precise relocation. Each group has a finite precision
budget:

```text
MAX_FIELD_ENUMERATION_EDGES
```

Count distinct primary `(initialAccess, finalAccess)` keys in the group. When
adding a batch would make the count exceed the budget:

1. remove every retained primary edge in that group;
2. mark the group permanently generalized;
3. retain its one projected representative;
4. publish the representative in the insertion delta;
5. absorb every later eligible edge in that group without re-enumerating it.

A value such as 64 makes the 401-edge reproduction deterministic while not
widening small ordinary field transfers. The constant must be configurable or
at least isolated so E2E performance/precision evaluation can tune it without
changing semantics.

The transition is monotone for IFDS consumers. Previously emitted concrete
edges are not retracted, but all later collection observes only the generalized
representative.

## Exclusions

The generalized representative uses `ExclusionSet.Empty`.

This is deliberate. Exclusions name precisely the field distinctions being
forgotten. Unioning them can exclude every enumerated field and make the
generalized edge fail to cover its contributors. This rule is specific to
field-erasing widening; it does not change exact-key exclusion intersection or
the existing fallback rule for a representation that merely merges different
exact finals.

## Storage organization

Keep exact subsumption and widening as two explicit stages in `add`:

```text
incoming edges
  -> exact-key exclusion merge
  -> exact correlated subsumption
  -> field-erasure budget/generalization
  -> immutable published snapshot and insertion delta
```

Required writer-owned state:

```text
exact edge aggregates
group membership for groups below budget
set of permanently generalized group keys
published canonical summaries
```

Once a group is generalized, its exact aggregates and membership can be
dropped. They are no longer needed because the empty-exclusion representative
cannot become narrower.

Collection does not perform generalization. It reads the published primary
snapshot, applies the existing initial-pattern filter, and derives normalized
trace views as it does today.

## Trace-resolution requirement

A synthesized generalized summary must have a resolvable method-side witness.
Publishing it only from
`MethodInitialToFinalBaseOnlyApSummariesStorage` is insufficient if backward
resolution still searches only the concrete
`MethodEdgesInitialToFinalBaseOnlyApSet` entries.

Before enabling the optimization, use one shared generalization operation for
both:

- the method-exit F2F edge set used by trace resolution; and
- the method F2F summary storage used by callers.

Alternatively, retain explicit provenance from the generalized summary to a
method-side generalized witness and teach trace resolution to consume that
witness. Retaining all concrete contributors as provenance is not acceptable:
it restores the same quadratic memory cost.

The generalized trace is an abstract witness, so it need not enumerate all
concrete read/write paths. It must, however, connect the method entry and exit
facts accepted by the generalized forward edge.

## Required tests

### End-to-end reproduction

- The 20-field sample finds the vulnerability.
- Before generalization it demonstrates the 401-edge family.
- After generalization the same method/base pair collects one field-erased
  summary and still finds the vulnerability.
- Tree remains the precision oracle; every Tree finding remains reachable in
  BaseOnly.

### Storage laws

- below-budget groups remain precise;
- crossing the budget replaces the group with one representative;
- all insertion orders produce the same final representation;
- a batch crossing the budget emits only the representative from that batch;
- later members of a generalized group do not re-expand it;
- different initial/final bases do not share a budget;
- different static prefixes do not merge;
- Normal/Value and semantic/type/final suffixes do not merge;
- the representative has empty exclusions even when contributors do not;
- unrelated summaries remain unchanged;
- normalized aliases remain collection-only.

### Consumer laws

- applying the generalized edge covers every forward result produced by each
  removed contributor;
- initial-pattern filtering returns the generalized edge for every compatible
  concrete field caller;
- full trace resolution succeeds through the generalized method-side witness;
- source-to-sink reachability survives after all concrete contributors have
  been discarded.

### Performance gate

Instrument retained primary summaries and summary applications. The 20-field
sample must retain one generalized member for the affected group rather than
401 members, and repeated calls must not recreate the concrete matrix.

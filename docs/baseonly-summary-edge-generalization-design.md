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

Correct conclusion subsumption first reduces this family to:

```text
1   field-abstract identity
20  concrete-field -> abstract-tail edges
--
21  F2F summaries
```

For each fixed `x`, the edge
`(-1, x, -2) -> (-1, -1, -2)` subsumes every
`(-1, x, -2) -> (-1, y, -2)`: the premise is identical and the abstract-tail
conclusion implies every concrete-field conclusion.

The desired bounded representation after structural-accessor generalization is:

```text
(-1, -1, -2) /E -> (-1, -1, -2) /E
```

This is an explicit field-erasing widening. It is not ordinary summary-edge
subsumption.

## Boundary between subsumption and generalization

An F2F summary is a correlated transformation. Under exact summary semantics,

```text
(-1, x, -2) -> (-1, -1, -2)
```

subsumes:

```text
(-1, x, -2) -> (-1, y, -2)
```

The premise is the same and the first conclusion directionally covers the
second. This is ordinary summary-edge subsumption and must happen before
generalization.

What subsumption does not remove is variation in the premise:

```text
(-1, x, -2) -> (-1, -1, -2)
(-1, z, -2) -> (-1, -1, -2)
```

Generalization forgets that remaining `x` versus `z` distinction. It
must remain a separate operation from `BaseOnlySummaryEdgeOps.subsumes`.

Generalization instead forgets which structural accessor was read and which
structural accessor was written. Structural accessors include ordinary fields
and the element accessor because implicit `[any]` covers both. Applying the
generalized edge produces an abstract final fact that covers every concrete
field and element accessor. False-positive paths are an accepted cost of the
widening; losing a forward result is not.

## Field-erasure projection

Generalization is local to one method entry, initial base, and final base.
Those bases are never merged. It is eligible only when both the initial and
final static slots are empty:

```text
initial.staticIdx == NO_ACCESSOR
final.staticIdx == NO_ACCESSOR
```

An edge with any non-empty static slot is never field-generalized. Such edges
are reduced only by ordinary summary-edge subsumption.

The eligible access shapes are:

```text
(-1, ABSTRACT_MARK, NO_ACCESSOR)
(-1, concreteFieldOrElement, ABSTRACT_MARK)
(-1, NO_ACCESSOR, ABSTRACT_MARK)
```

They all project to:

```text
eraseField(access) = (NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
```

Normal and Value suffix states, semantic marks, type-information accessors, and
final accessors must not be merged. `ANY_ACCESSOR` itself remains implicit and
is never stored in the field slot.

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

Count distinct primary `(initialAccess, finalAccess)` keys remaining after
ordinary subsumption. When adding a batch would make the count exceed the
budget:

1. remove every retained primary edge in that group;
2. mark the group permanently generalized;
3. retain its one projected representative;
4. publish the representative in the insertion delta;
5. absorb every later eligible edge in that group without re-enumerating it.

A value below 20, such as 16, makes the 20-field reproduction deterministic
after conclusion subsumption has reduced it to 21 edges, while not widening
small ordinary field transfers. The constant must be configurable or at least
isolated so E2E performance/precision evaluation can tune it without changing
semantics.

The transition is monotone for IFDS consumers. Previously emitted concrete
edges are not retracted, but all later collection observes only the generalized
representative.

## Exclusions

The generalized representative uses the union of every member exclusion:

```text
E = E1 union E2 union ... union En
```

The suffix remains `ABSTRACT_MARK` after structural-accessor erasure, so the
exclusions still belong to that suffix and must be retained. A later absorbed
member extends this union; if the union changes, storage publishes the updated
representative as an insertion delta. Exact-key exclusion intersection remains
unchanged before generalization.

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
dropped. The group key and accumulated exclusion union remain so later members
can update the representative without restoring accessor enumeration.

Collection does not perform generalization. It reads the published primary
snapshot, applies the existing initial-pattern filter, and derives normalized
trace views as it does today.

## Trace-resolution requirement

A synthesized generalized summary must have a resolvable method-side witness.
Publishing it only from
`MethodInitialToFinalBaseOnlyApSummariesStorage` is insufficient if backward
resolution still searches only the concrete
`MethodEdgesInitialToFinalBaseOnlyApSet` entries.

The method F2F fact set remains exact during forward analysis. It must not
replace or emit exact edges with generalized edges.

As a temporary trace-resolution bridge, `BaseOnlyApManager` has a one-way
trace-resolution mode. While that mode is disabled, fact-set insertion and
collection retain their original exact behavior. While it is enabled,
collection may additionally project eligible exact witnesses into the same
field-erased shape used by summary storage. This trace view does not apply the
summary-storage budget: a statement containing one eligible exact edge may
witness a generalized method summary created from edges accumulated elsewhere.
The projected edge is never inserted into the fact set and never enters the
forward worklist.

The generalized trace is an abstract witness, so it need not enumerate all
concrete read/write paths. It must, however, connect the method entry and exit
facts accepted by the generalized forward edge.

## Required tests

### End-to-end reproduction

- The 20-field sample finds the vulnerability.
- Before the corrected subsumption it demonstrates the 401-edge family.
- Correct conclusion subsumption reduces it to 21 retained edges.
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
- any edge with a non-empty initial or final static slot is never generalized;
- static-prefixed edges continue to use ordinary subsumption;
- Normal/Value and semantic/type/final suffixes do not merge;
- the representative has the union of all contributor exclusions;
- element-accessor members participate in the same budget as field members;
- a later absorbed member updates and re-emits the representative only when
  its exclusion grows the union;
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
sample must progress from 401 current members to 21 after corrected
subsumption, then to one generalized member. Repeated calls must not recreate
the concrete matrix.

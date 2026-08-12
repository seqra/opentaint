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

The budget is 8: eight distinct canonical field transfers remain exact and the
ninth generalizes the group. This makes the 20-field reproduction deterministic
without aggressively widening ordinary one-off field transfers. The constant
is isolated so E2E performance/precision evaluation can tune it without
changing semantics.

The transition is monotone for IFDS consumers. Previously emitted concrete
edges are not retracted, but all later collection observes only the generalized
representative.

## Exclusions

Field/element/static exclusions describe structural accessors erased by the
projection. They are therefore removed before member exclusions are combined.
Only exclusions that can occur in the remaining suffix slot are retained.

```text
project(E) = E without field, element, static, or Any accessors
```

After projection, the generalized members are alternative edges with the same
premise and conclusion. Their exclusions are intersected:

```text
E = project(E1) intersect project(E2) ... intersect project(En)
```

Union is incorrect here: an exclusion belonging to one erased premise would
then reject a suffix accepted by another member, producing a false negative.
A later absorbed member can only keep or shrink the representative exclusion.
If it shrinks, storage publishes the updated representative as an insertion
delta. Exact-key exclusion intersection remains unchanged before
generalization.

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
dropped. The group key and common projected exclusion remain so later members
can update the representative without restoring accessor enumeration.

Collection does not perform generalization. It reads the published primary
snapshot, applies the existing initial-pattern filter, and derives normalized
trace views as it does today.

## Fact-set and trace boundary

Summary-storage generalization does not require or enable fact-set
generalization. `summaryStorageFieldGeneralizationEnabled` controls only the
F2F summary storage. The pre-existing `fieldGeneralizationEnabled` trace view
is independent, remains disabled by default, and is not changed by this
feature. The method F2F fact set therefore remains exact in the configuration
used by summary generalization.

The supported summary-generalization configuration keeps
`fieldGeneralizationEnabled` false. Enabling both mechanisms would give the
summary representative and the trace-only fact view different exclusion
reducers and is outside this design.

When resolving a generalized summary, the existing BaseOnly compatibility
relation selects its concrete method-side witnesses. Each selected witness
must connect an exact member premise and conclusion covered by the generalized
edge. The end-to-end regression test must resolve a complete trace with
summary generalization enabled and fact/trace generalization disabled.

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
- a later member that shrinks the common suffix exclusion publishes the
  broader representative;
- different initial/final bases do not share a budget;
- any edge with a non-empty initial or final static slot is never generalized;
- static-prefixed edges continue to use ordinary subsumption;
- Normal/Value and semantic/type/final suffixes do not merge;
- the representative intersects suffix-valid contributor exclusions;
- structural exclusions erased by projection are not retained;
- element-accessor members participate in the same budget as field members;
- a later absorbed member updates and re-emits the representative only when
  its common suffix exclusion shrinks;
- unrelated summaries remain unchanged;
- normalized aliases remain collection-only.
- summary-storage and fact-trace generalization flags are independent in both
  directions.

### Consumer laws

- applying the generalized edge through the real delta/concat/exclusion
  refinement path covers every forward result produced by each removed
  contributor;
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

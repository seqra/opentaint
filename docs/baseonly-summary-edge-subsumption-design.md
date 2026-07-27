# BaseOnly F2F summary-edge subsumption

## Goal

`MethodInitialToFinalBaseOnlyApSummariesStorage` must retain an antichain of
summary edges. For two edges with the same entry base, exit base, and exit
statement, an edge can be discarded when every forward application and every
backward trace reconstruction provided by it is already provided by one other
edge.

For example:

```text
this.a.*    /{} -> this.b.*    /{}
this.a.MARK /{} -> this.b.MARK /{}
```

The second edge is redundant. Applying the first edge to `this.a.MARK` extracts
the residual `MARK` and grafts that same residual onto `this.b.*`, producing
`this.b.MARK`. Backward resolution performs the inverse operation and rebuilds
`this.a.MARK`.

Subsumption is pairwise. The first implementation does not need to prove that a
union of several existing edges covers a new edge.

## Semantic relation

Let an edge be:

```text
E = (initial, final, exclusions)
```

Define:

```text
subsumes(cover, covered)
```

as directional inclusion of the summary transformations, not independent
containment of the two access paths.

### Residual correlation

It is incorrect to use only:

```text
covers(cover.initial, covered.initial) &&
covers(cover.final, covered.final)
```

The initial and final sides of an F2F edge are correlated by one residual. For
example, `a.* -> b.*` covers `a.M -> b.M`, but it does not cover
`a.M -> b.N`.

The authoritative predicate must therefore:

1. apply `cover` to `covered.initial` using the same residual operation as
   `FinalFactAp.delta`;
2. graft each surviving residual onto `cover.final` using the same operation as
   `FinalFactAp.concat`;
3. accept only if one produced final fact, including its effective exclusions,
   subsumes `covered.final / covered.exclusions`;
4. verify that backward `InitialFactAp.splitDelta` on `covered.final` and
   `cover.final` can recover the same residual and that concatenating it with
   `cover.initial` directionally covers `covered.initial`.

In notation, for at least one residual `d`:

```text
d in residual(covered.initial, cover.initial, cover.exclusions)
factSubsumes(apply(cover, covered.initial / covered.exclusions),
             covered.final / covered.exclusions)

d in splitResidual(covered.final, cover.final, cover.exclusions)
covers(concat(cover.initial, d), covered.initial)
```

The two witnesses must denote the same logical residual. Checking the forward
and backward conditions independently without correlating their residuals can
accept an edge that works in analysis but cannot resolve a trace.

This should be implemented once as:

```kotlin
BaseOnlySummaryEdgeOps.subsumes(cover, covered): Boolean
```

The implementation should use shared access-level residual, exclusion, graft,
and concat operations. It must not duplicate AP-slot case logic in the storage.

`factSubsumes` is likewise directional and operational. It asks whether the
first final fact can be applied as a summary pattern to obtain the second fact.
For a non-empty residual, the first fact's exclusions are applied to that
residual. For an empty residual, exclusion permissiveness is compared. This is
more precise than either raw access coverage or whole-set exclusion comparison.

### Empty residual and exclusions

If `cover.initial == covered.initial`, both edges apply with an empty residual.
The final fact produced by `cover` has:

```text
effective exclusions =
    covered.exclusions union cover.exclusions
```

That produced final fact is compared to
`covered.final / covered.exclusions` with `factSubsumes`. When the final
accesses are also equal, this reduces to:

```text
covered.exclusions.contains(cover.exclusions)
```

When `cover.final` is broader, an exclusion may be irrelevant to the concrete
branch represented by `covered.final`; the residual operation decides that
case. A blanket exclusion-subset requirement would retain redundant edges.

For equal `(initial, final)` keys, additions continue to merge exclusions by
intersection before any subsumption check.

For a non-empty residual, `cover.exclusions` is checked by the ordinary
residual operation. If it rejects the residual, `cover` does not subsume the
edge. If it accepts the residual, its exclusions are not copied to the mapped
fact by summary application, so a separate whole-set subset check would be
unnecessarily restrictive.

Normalized initial aliases are collection-only trace views. They do not
participate in primary-edge subsumption.

## Add protocol

All incoming edges are first consolidated by exact `(initial, final)` key,
intersecting their exclusions. The storage writer then processes each
consolidated edge:

1. Reject collapsed or invalid accesses as today.
2. Merge an existing exact key by exclusion intersection. Treat the merged
   record as the candidate; a less restrictive exclusion can make it subsume
   additional records.
3. Find active records whose initial access may be a prefix of the candidate
   initial. Apply the authoritative `subsumes(existing, candidate)` predicate.
   If one succeeds, ignore the candidate.
4. Find active records whose initial access may extend the candidate initial.
   Apply `subsumes(candidate, existing)` and tombstone every successful match.
5. Publish the candidate and mark only it as insertion delta.

Steps 3 and 4 use an index only to obtain a conservative candidate set. The
authoritative predicate is always evaluated before rejection or removal.

If two different representations mutually subsume one another, choose a stable
winner with a deterministic canonical key order. This makes the final
antichain independent of insertion order.

Delta collection occurs after the whole input batch, as it does today. Thus an
edge inserted and then subsumed by a later edge in the same batch emits no
delta. Removing an edge published by an earlier call emits no retraction: the
new edge covers its behavior, and IFDS propagation remains monotone.

## Storage changes

Keep the current specialized identity and non-identity physical layouts. Add a
writer-side subsumption index spanning both, because an identity and a
non-identity edge must not be treated as separate semantic universes.

Each indexed record has a handle to its physical leaf. A physical leaf supports:

```kotlin
updateExclusion(intersection): Boolean
remove()
isActive(): Boolean
```

Removal sets the leaf payload to `null`; it does not remove or compact parent
nodes. Empty per-initial storages remain in the index and may be traversed, but
emit no summaries. This follows the existing single-writer/multiple-reader
storage approach and avoids structural mutation visible to concurrent readers.

The existing local abstraction logic in `StaticLayer`, `FieldLayer`, and
`SuffixLayer` must report every leaf it nulls so the spanning index cannot
retain an apparently active stale record. Alternatively, move all local
subsumption decisions into the new authoritative edge predicate and make the
physical tries exact-key stores. There must be only one authority for deciding
whether a record is active.

The initial-access candidate index needs two directional traversals:

```kotlin
collectPotentialPrefixes(access, consume)
collectPotentialExtensions(access, consume)
```

They may over-return. Unlike `collectCandidates`, these methods must not use
the symmetric `mayOverlap` relation as the final decision.

The concurrency contract remains:

```text
one writer, multiple eventually-consistent readers
```

Record exclusion and active-leaf publication must be visible to readers.
Readers may observe an old covered record or the new covering record during an
insertion, but must never observe a malformed edge. After the writer completes,
later readers observe only the antichain.

## Required tests

### Core examples

- `a.* -> b.*` subsumes `a.M -> b.M`, in both insertion orders.
- `a.* -> b.*` does not subsume `a.M -> b.N`.
- `a.* -> b.M` does not subsume `a.N -> b.M` when graft cannot preserve the
  residual.
- `Normal` and `Value` terminal modes remain distinct.
- identity/non-identity cross-storage candidates are checked.

### Exclusions

- an abstract edge excluding `M` does not subsume the concrete `M` edge;
- for equal initials, `{}` subsumes `{M}`, but `{M}` does not subsume `{}`;
- exact-key updates intersect exclusions and rerun eviction;
- an exclusion unrelated to a non-empty residual does not by itself prevent
  subsumption.

### Storage and delta

- a batch containing narrow then broad emits only the broad delta;
- a previously published narrow edge disappears from later collection after a
  broad edge is added;
- all permutations produce the same canonical antichain;
- patterned and full collection never return tombstoned records;
- normalized views are derived only from active primary records.

### Forward/trace differential

For a bounded set of Tree-equivalent accesses and caller extensions:

1. apply both edges and record all forward outputs;
2. remove the edge classified as covered and repeat;
3. assert that every previous output is directionally covered;
4. resolve backward from every output and assert that every previous entry
   precondition is directionally covered.

Also test reflexivity and transitivity of the predicate on generated canonical
edges. A transitivity counterexample is a release blocker because permanent
tombstones rely on a chain of newer covering edges continuing to cover every
older removed edge.

### Concurrent readers

Force map rehashes while one writer repeatedly replaces narrow edges with broad
ones and several readers perform full and patterned collection. Assert no
exception or malformed edge, then join the writer and assert eventual
antichain completeness.

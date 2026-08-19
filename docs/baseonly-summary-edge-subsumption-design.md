# BaseOnly F2F summary-edge subsumption

## Goal

`MethodInitialToFinalBaseOnlyApSummariesStorage` has two operations:

- `add` merges new summaries into a minimal covering set and reports its
  insertion delta;
- `collect` returns the retained summaries matching an optional initial-fact
  pattern, including normalized read-only views when enabled.

The storage does not expose separate forward and backward modes. Edge
subsumption is an internal decision made by `add`. Its predicate must preserve
the correlated transformation used by every consumer of a collected summary.

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

1. handle equal premises by directional conclusion coverage: if the initial
   facts are equal, `cover` subsumes `covered` when `cover.final` contains
   `covered.final`, subject to the exclusion rules below;
2. otherwise apply `cover` to `covered.initial` using the same residual operation as
   `FinalFactAp.delta`;
3. graft each surviving residual onto `cover.final` using the same operation as
   `FinalFactAp.concat`;
4. accept only if one produced final fact, including its effective exclusions,
   is exactly `covered.final / covered.exclusions`;
5. verify that backward `InitialFactAp.splitDelta` on `covered.final` and
   `cover.final` can recover the same residual and that concatenating it with
   `cover.initial` exactly reconstructs `covered.initial`.

The equal-premise rule is implication between two conclusions, not residual
grafting. For example:

```text
(-1, x, -2) -> (-1, -1, -2)
```

subsumes:

```text
(-1, x, -2) -> (-1, y, -2)
```

because `(-1, -1, -2)` contains `(-1, y, -2)`. Requiring exact final equality
in this case incorrectly retains every enumerated `y`.

In notation, for at least one residual `d`:

```text
d in residual(covered.initial, cover.initial, cover.exclusions)
apply(cover, covered.initial / covered.exclusions)
    == covered.final / covered.exclusions

d in splitResidual(covered.final, cover.final, cover.exclusions)
concat(cover.initial, d) == covered.initial
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

Directional BaseOnly coverage is not sufficient here. In particular, implicit
`AnyAccessor` makes `.*` cover `.f.*`, but the transformations `.* -> .*` and
`.* -> .f.*` are not trace-equivalent: the latter installs the residual under
`f`. Deleting it loses the backward field-installation step. Exact correlated
reconstruction is intentionally conservative; a retained redundant edge costs
space, while a falsely deleted edge loses trace behavior.

### Empty residual and exclusions

If `cover.initial == covered.initial`, both edges apply with an empty residual.
The final fact produced by `cover` has:

```text
effective exclusions =
    covered.exclusions union cover.exclusions
```

That produced final fact must equal
`covered.final / covered.exclusions`. Since the final accesses must be equal,
the exclusion check reduces to:

```text
covered.exclusions.contains(cover.exclusions)
```

Exclusions are intersected only for repeated occurrences of the same exact
`(initial, final)` edge. Different finals retain independent exclusions.

If a representation forces several distinct final edges into one record, their
exclusions must instead be combined by union. BaseOnly stores the finals
separately, so this lossy fallback is unnecessary.

For a non-empty residual, `cover.exclusions` is checked by the ordinary
residual operation. If it rejects the residual, `cover` does not subsume the
edge. If it accepts the residual, its exclusions are not copied to the mapped
fact by summary application, so a separate whole-set subset check would be
unnecessarily restrictive.

Normalized initial aliases are collection-only trace views. They do not
participate in primary-edge subsumption.

## Add protocol

The storage writer handles one `add` batch as follows:

1. Reject edges containing a collapsed access.
2. Intersect every incoming exclusion into the aggregate for its exact
   `(initial, final)` key.
3. Rebuild the retained and incoming records for the affected exact keys.
4. Combine those rebuilt candidates with summaries for unaffected keys and
   retain a deterministic antichain using the authoritative `subsumes`
   predicate.
5. Publish the complete new snapshot and append every newly visible primary
   summary to the insertion delta.

Steps 3 and 4 use an index only to obtain a conservative candidate set. The
authoritative predicate is always evaluated before rejection or removal.

If two different representations mutually subsume one another, choose a stable
winner with a deterministic canonical key order. This makes the final
antichain independent of insertion order.

Delta collection occurs after the whole input batch, as it does today. Thus an
edge inserted and then subsumed by a later edge in the same batch emits no
delta. Removing an edge published by an earlier call emits no retraction: the
new edge covers its behavior, and IFDS propagation remains monotone.

## Collect protocol

`collect` reads one immutable snapshot of the retained primary summaries:

1. Add each primary summary that matches the optional initial-fact pattern.
2. When normalized views are enabled, derive the normalized initial from each
   primary and add it if it matches the pattern.
3. Merge duplicate `(initial, final)` views by exclusion intersection.
4. Materialize the resulting summary builders.

Normalized views have no independent storage state and never contribute an
insertion delta.

## Storage representation

The logic-first implementation keeps:

- writer-owned merged exclusions keyed by exact `(initial, final)` edge;
- one volatile immutable list of retained primary summaries.

`add` computes and publishes a complete replacement list. `collect` reads only
that published list. Identity and non-identity edges share the same
representation and the same subsumption authority.

The concurrency contract remains:

```text
one writer, multiple eventually-consistent readers
```

Snapshot publication must be visible to readers. A reader may observe the
complete old snapshot or the complete new snapshot during an insertion, but
never a partially rebuilt set. After the writer completes, later readers
observe the new antichain.

## Required tests

### Core examples

- `a.* -> b.*` subsumes `a.M -> b.M`, in both insertion orders.
- `a.* -> .*` subsumes `a.* -> b.*`: the premise is identical and the first
  conclusion contains the second.
- `(-1, x, -2) -> (-1, -1, -2)` subsumes
  `(-1, x, -2) -> (-1, y, -2)`.
- `a.* -> b.*` does not subsume `a.M -> b.N`.
- `a.* -> b.M` does not subsume `a.N -> b.M` when graft cannot preserve the
  residual.
- `Normal` and `Value` terminal modes remain distinct.
- identity/non-identity cross-storage candidates are checked.

### Exclusions

- an abstract edge excluding `M` does not subsume the concrete `M` edge;
- for equal initials, `{}` subsumes `{M}`, but `{M}` does not subsume `{}`;
- exact-key exclusion updates rerun eviction without changing unrelated
  finals;
- an exclusion unrelated to a non-empty residual does not by itself prevent
  subsumption.

### Storage and delta

- a batch containing narrow then broad emits only the broad delta;
- a previously published narrow edge disappears from later collection after a
  broad edge is added;
- all permutations produce the same canonical antichain;
- patterned and full collection never return tombstoned records;
- normalized views are derived only from active primary records.

### Consumer differential

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

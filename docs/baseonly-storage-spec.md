# BaseOnly storage specification

## Status and scope

This document is the normative specification for storage owned by the BaseOnly access-path implementation. It covers intraprocedural edge sets, method-summary stores, side-effect stores, subscriptions, the final-fact stack, and the indexes used by those stores.

The BaseOnly access-domain specification defines canonical accesses and these semantic operations:

- `concretize(A)`: the concrete Tree paths denoted by `A`;
- `covers(A, B)`: directional inclusion, `concretize(B) ⊆ concretize(A)`;
- `mayOverlap(A, B)`: symmetric non-empty intersection;
- `residual(P, F)`: the deltas by which `F` extends a matched pattern `P`.

This document does not redefine those operations. A storage must call their shared production implementation. Packed-slot compatibility is not a storage relation.

Tree is the behavioral reference. BaseOnly may store or return a less precise representation, but for the same inserted projected edges it must not omit behavior returned by Tree:

```text
project(denotation(Tree result)) ⊆ denotation(BaseOnly result)
```

This is a denotational requirement. Tree may merge several paths into one access tree while BaseOnly returns several records, or conversely BaseOnly may return one widened record. Collection shape and iteration order are not observable semantics.

The words **must**, **must not**, **should**, and **may** are normative.

## Terms

### Fact and edge identity

A fact is the tuple:

```text
Fact = (base, canonical access, exclusions)
```

An edge contains the bases and accesses named in the per-storage tables below. Exclusions are edge payload unless explicitly included in a logical key. Statement and method/exit-point partitioning performed by common storage wrappers is part of the key even when it is outside the BaseOnly leaf structure.

Two records are the same logical record when all key components are equal after canonicalization. Object identity, packed construction history, insertion order, bucket, and normalized-view origin are never key components.

Value-accessor state is part of canonical access identity. For the same compact
semantic accessor, `Normal` and `Value` are distinct keys and denote different
paths. An index may route them through the same suffix bucket, but must compare
the full access before lookup or publication.

### Record denotation and subsumption

The denotation of a stored record is the set of concrete Tree facts or edges represented by its canonical BaseOnly access values and exclusions. A record `R1` subsumes `R2` exactly when:

```text
denotation(R2) ⊆ denotation(R1)
```

Directional `covers` is used to prove access inclusion inside this definition. `mayOverlap` cannot prove subsumption.

A store may physically retain a subsumed record, but one collection must not emit duplicate logical behavior. Physical pruning is an optimization and must preserve the single-writer/multiple-reader publication rules.

### Query applicability

For a nullable access pattern `P` and stored initial access `I`:

```text
applicable(P, I) = P == null || mayOverlap(P, I)
```

This is the authoritative predicate for F2F-summary and fact-side-effect lookup. It captures Tree's `filterContains`: a Tree query can select a stored prefix or a stored descendant represented by an abstract pattern. The BaseOnly result must include every projected Tree result. Exclusions remain attached to returned records and do not remove index candidates.

An index may return a strict superset of applicable records. Every candidate must pass `applicable` before emission. An index must never use `covers` in one arbitrary direction as a substitute for overlap.

### Transient collapsed values

`COLLAPSED_MARK` belongs only to the `removeAbstraction`/`rebase` flow-function
lifecycle. Every BaseOnly insertion boundary checks `access.isCollapsed` before
mutating keys, payloads, deltas, indexes, or subscriptions. Stable accesses are
inserted directly; there is no probing predicate and no exception-driven
classification. The common storage implementations remain unchanged.

## Exclusion algebra

`ExclusionSet` has the ordinary set order:

```text
Empty ⊆ Concrete ⊆ Universe
```

`union` and `intersect` mean set union and intersection. Storage merge direction follows the denotation of the record, not a universal rule.

### Alternative-flow merge

When two records in the same logical edge aggregate describe alternative executions, their represented behaviors are united. For an open access with exclusions, the union of the two allowed languages excludes only accessors excluded by both alternatives. Therefore:

```text
mergeAlternative(E1, E2) = E1 intersect E2
```

This applies to method F2F summaries, including identity and non-identity summaries. It matches Tree's identity exclusion merge and Tree's per-initial non-identity summary merge.

### Fact-state merge

When two intraprocedural F2F facts at the same statement/key accumulate known exclusions as fact state, the stored exclusion is:

```text
mergeFactState(E1, E2) = E1 union E2
```

This matches `MethodEdgesInitialToFinalTreeApSet`.

### Side-effect merge

For the same fact-side-effect key or side-effect-requirement key, exclusions accumulate by union:

```text
mergeSideEffect(E1, E2) = E1 union E2
```

This matches Tree side-effect summary and requirement storage.

### Merge laws

Every merge operator used by a storage must be associative, commutative, and idempotent. Consequently, final state is independent of batch boundaries and insertion order.

When stored alternatives contain paths with the same prefix and semantic
accessor but different value-accessor states, they remain separate records:

```text
Normal join Normal = { Normal }
Value join Value   = { Value }
Normal join Value  = { Normal, Value }
```

The union is represented by two facts, never by a third packed state. Query
matching, subsumption, deltas, and normalized aliases process and preserve each
state independently.

If a batch updates one logical aggregate more than once, the persistent storage
merges each update immediately and coalesces writer-local delta keys until the
batch is drained. A logical delta may require several builders when the
final-access language is materialized as several canonical accesses; each
required component is emitted at most once. The drained delta contains the full
final-access language with the final aggregate for exclusion-only changes, and
may contain only the newly admitted final-access behavior when the exclusion is
unchanged. It must never contain an intermediate exclusion value.

## Ownership and concurrency

### Summary and side-effect stores

Method Z2F, F2F, and ND summary stores, fact-side-effect stores, and side-effect-requirement stores use this contract:

```text
one writer; zero or more concurrent readers; eventually consistent
```

The effective writer is serialized by the analyzer. Readers do not acquire the writer monitor.

A reader may observe an older complete state and may omit an insertion concurrent with that query. A later query after writer completion must observe the committed insertion. A reader must never observe:

- a value before all required fields are initialized;
- a transient default such as `Universe` that was never committed;
- a key paired with a value from another table generation;
- a malformed/null record;
- a transient collapsed record rejected before insertion;
- two emissions of the same logical view in one query;
- an exception caused by concurrent insertion or rehash.

Shared indexes are append-only under this contract. Concurrent-read-safe primitive maps/sets must use captured-generation point reads and traversal. Inherited fastutil iterators are forbidden. Values must be fully initialized before the key or parent link is published. A mutable value visible to readers must publish complete immutable replacements, or use a holder with an equivalent proven publication protocol.

Subsumption must not physically remove an entry from an append-only SWMR index. It must use immutable replacement/tombstone state that readers can interpret safely, or leave the entry in place and suppress it with the authoritative denotational check. Rebuilding and atomically publishing an immutable root is also valid.

Delta accumulators are writer-owned and are never read concurrently. They use ordinary collections and are drained once per writer batch.

### Intraprocedural fact sets and final-fact lists

Intraprocedural Z2F/F2F/ND edge sets and `FinalFactList` are single-analysis-thread-owned. Ordinary primitive maps, sets, arrays, and lists are correct. Adding concurrent structures to these stores is not required and must not alter their semantics.

### Subscription registries

Subscription registration and collection are analysis-thread-owned under the current workload. Ordinary collections are correct. If subscription lookup is later moved to concurrent readers, that is a contract change and requires the SWMR rules above; it must not be inferred from summary-store concurrency.

## Shared initial-access index

`BaseOnlyInitialAccessIndex<V>` is a candidate index, not a semantic store. Its logical key is one canonical initial access. It must provide:

```text
getOrCreate(I)
collectAll()
collectCandidates(P)
```

The key preserves the complete canonical access, including value-accessor state. Slot projections
such as `(staticIdx, fieldIdx, suffixIdx)` are routing dimensions only and must not merge accesses
whose packed value-accessor states differ.

`collectCandidates(P)` must be complete:

```text
applicable(P, I) implies I is visited
```

It may visit non-applicable `I`. Callers must apply `applicable(P, I)` after traversal. The index must not merge different canonical keys, own exclusions, emit deltas, or normalize accesses.

Tree comparison: Tree's `AccessBasedStorage.filterContains` is the semantic reference, including stored prefixes, abstract-pattern descendants, and Any behavior. For bounded projected Tree inputs, every Tree-selected initial must occur in the BaseOnly candidate set and pass the BaseOnly authoritative predicate.

Index laws:

- exact lookup returns the value for the exact canonical key;
- full collection returns every published key at most once;
- patterned collection is complete for `applicable`;
- insertion and candidate results are independent of insertion order;
- after the writer completes, indexed candidates equal a scan-and-predicate reference after authoritative filtering;
- a query during rehash returns a subset of one or more complete published generations, never a malformed pair.

## Intraprocedural storage

These stores are single-threaded and keyed by the common method edge partitions plus the BaseOnly components below.

| Store | BaseOnly logical key | Merge/result | Tree relation |
|---|---|---|---|
| Z2F edge set | `(statement, final base, final access)` | Exact set union; exclusions are `Universe` | Denotation equals or covers Tree's merged access tree at the statement |
| F2F edge set | `(statement, initial base, initial access, final base)` with final-access language as payload | Union final-access denotations; one aggregate exclusion merged with `mergeFactState` | Covers Tree's per-initial merged final tree and uses Tree's exclusion union |
| ND edge set | `(statement, final base, canonical set of initial facts with Universe exclusions)` with final accesses as payload | Exact set/denotational union of finals | Covers Tree's merged final tree for the same initial set |
| Final-fact list | stack position | Preserve exact `(base, access, exclusions)`; LIFO remove | Same ordered stack behavior as Tree; no access merge |

Collapsed values contribute nothing. `add` returns no delta when the inserted denotation is already represented. If BaseOnly retains multiple accesses where Tree returns one tree, collection returns their denotational union; callers must not depend on cardinality or order.

Intraprocedural F2F lookup with an explicitly supplied initial uses exact canonical initial access, as Tree does. A normalized summary alias is not an intraprocedural fact-set key and must not be stored in this set. If trace resolution needs an alias, it is applied at summary query time.

## Method-summary storage

Method summaries are partitioned by method entry/exit point and bases in the common layer. The following sections specify the BaseOnly leaf state.

### Z2F summaries

Logical key:

```text
(final base, final access)
```

Exclusions are `Universe`. Insertion is denotational set union. The writer emits a delta only for newly admitted final-access behavior. Collection returns every current logical final once.

Tree comparison: Tree merges all Z2F finals for the same partition into one access tree. The union of BaseOnly results must cover the projection of that tree. BaseOnly result cardinality is not required to equal Tree cardinality.

### F2F summaries

The primary non-identity aggregate key is:

```text
(initial base, initial access, final base)
```

Its payload is the union of final-access languages and one exclusion value merged with `mergeAlternative` across every alternative in the aggregate. BaseOnly may materialize that language as several canonical final accesses, but every emitted component reads the aggregate's current exclusion. It must not retain a different exclusion per exact final: that would preserve a correlation that Tree deliberately loses when it merges the final tree and intersects exclusions.

The identity aggregate key is `(initial base, initial access, final base)` plus the fact that its payload denotes the identity portion extracted from the final language. Identity is an optimization class only; it does not define a different exclusion algebra or query relation.

For each writer batch:

1. canonicalize and validate all accesses;
2. split identity and non-identity behavior by the shared access operation;
3. incrementally merge each edge into its persistent aggregate;
4. update candidate/subsumption indexes as part of that aggregate insertion;
5. record the changed persistent aggregate in writer-local delta state;
6. after all inputs are stored, emit one logical primary delta per changed
   aggregate, materialized as each required final-access component exactly once.

No temporary batch aggregate duplicates the persistent identity trie or
non-identity merging storage. The persistent structures are the sole source of
merge and subsumption semantics.

Identity summaries follow Tree's exclusion-aware hierarchical subsumption.
Repeated insertion of the same canonical access intersects exclusions. An
abstract access suppresses a concrete identity only when the concrete accessor
is a child in that same packed/logical slot and is not present in the abstract
edge's exclusions. A `NO_ACCESSOR` advances to a later slot and is not a child
edge, so `(NO_ACCESSOR, field-AP, NO_ACCESSOR)` does not subsume
`(NO_ACCESSOR, NO_ACCESSOR, suffix)`. Normal and Value suffix children are
distinct keys; a suffix abstraction may suppress both when their shared
semantic accessor is permitted. Patterned collection obtains conservative
candidates and applies `mayOverlap`.

Patterned collection uses `applicable(pattern, storedInitial)`. The initial-access index only chooses candidates; the final predicate is mandatory. Full collection uses a null pattern. Each materialized component `(aggregate identity, final access, aggregate exclusion)` is emitted at most once.

Tree comparison:

- Tree detects identity behavior with `splitOnMatching` and stores it in an exclusion-aware trie. BaseOnly must cover that identity denotation whether it classifies the record as identity or non-identity.
- Tree merges non-identity final trees per initial and intersects alternative-flow exclusions. The union of BaseOnly components for that initial must cover the projected Tree summary, and all components must expose the same merged exclusion.
- Tree's `filterContains` determines pattern applicability. BaseOnly must include every projected result and may include only results allowed by `mayOverlap`.

### Normalized F2F aliases

A normalized access is a query-time view of one primary F2F record. It is not a second summary record.

For a materialized primary component `R`, normalization may produce zero or more exposed initial accesses `aliasInitial(R)`. A collected view has identity, within the common base/exit partitions:

```text
(exposed initial access, primary final-access component)
```

The alias:

- owns no exclusion state;
- reads the current exclusion from its primary record;
- owns no delta accumulator;
- emits no insertion/update delta;
- owns no independent subscription state;
- cannot outlive or diverge from its primary record;
- participates in a conservative trace-query candidate view;
- is generated by one shared normalization operation.

Primary and alias views with the same exposed initial/final are emitted once. If
several primary aggregates expose that same view, their exclusions are intersected
as alternative flows at collection time; the alias still owns no independent state.
A primary and alias view with different exposed initials may both be emitted because
they are distinct trace alternatives.

Trace-query collection may scan all primary components in the selected method/base storage and
emit both primary and alias views even when the packed query pattern does not satisfy the ordinary
forward `applicable` predicate. This is required because the projected query can match an alias
whose primary initial is outside the packed candidate bucket. The backward trace resolver's
entry-edge containment/residual check is authoritative. This conservative view does not change
primary state, forward deltas, or forward subscription fan-out.

Alias availability is selected by the analyzer's explicit one-way transition from
forward queries to trace-resolution queries. Each storage query captures that
phase once at entry, so a transition cannot change the meaning of an
already-running query. There is no general-purpose mutable alias toggle.

Tree comparison: aliases exist only to preserve a Tree-resolvable backward match lost by BaseOnly projection. Adding an alias must not add a forward summary delta or a second forward fact. For each Tree summary applicable to a query, the primary/alias view union must contain an applicable BaseOnly view.

### ND F2F summaries

Logical key:

```text
(final base, canonical set of initial facts with Universe exclusions, final access)
```

Initial-set equality is order-independent. Repeated final accesses are idempotent. A writer batch emits each newly admitted final-access behavior once for its initial set.

A query with no initial pattern scans all initial sets. A query with pattern base `B` considers only initial sets containing an initial fact with base `B`; access-level filtering of each returned final then follows the summary application operation, not an unrelated base-wide broadcast. If the public query provides enough access information to filter before return, the implementation should use it, but filtering must remain a complete overapproximation of Tree.

Tree comparison: Tree indexes initial facts by base and merges final trees per equal initial set. BaseOnly must select every Tree-relevant initial set and its final-access union must cover the projected Tree final tree.

## Side-effect storage

### Fact-side-effect summaries

Logical key:

```text
(initial base, initial access, side-effect kind)
```

Repeated exclusions merge with `mergeSideEffect`. A batch emits at most one final aggregate per changed key. Patterned lookup uses `applicable(pattern, initialAccess)` through the shared initial-access index and authoritative predicate. Null pattern performs a full scan.

Tree comparison: Tree uses `AccessBasedStorage.filterContains` and union-merges exclusions per kind. BaseOnly must return every projected Tree-selected side effect with an exclusion set that does not remove Tree behavior.

### Side-effect requirements

Logical key:

```text
(required base, required initial access)
```

Repeated exclusions merge with `mergeSideEffect`. `add` applies requirements
incrementally in input order and drains each modified storage's accumulated
delta after insertion; it does not pre-coalesce the input batch.
`collectAllRequirementsTo` returns every current logical requirement once.

`filterTo(fact)` first selects the exact base, then returns only requirements whose initial access is applicable to the fact's final access. It must not broadcast every requirement for the base.

Tree comparison: Tree calls `filterContains(fact.access)` and returns only matching requirement nodes. The BaseOnly result must include every projected Tree match and must pass the BaseOnly `mayOverlap` predicate.

## Subscription storage

Subscriptions store caller edges waiting for a callee summary whose initial fact is `P`. Registration deduplicates the full caller-side logical key; it does not merge unrelated caller initials or exits.

All Z2F, F2F, and ND lookup uses one shared candidate operation:

```text
subscriptionCandidates(registrations, P, mode) -> superset of applicable registrations
```

The result is a candidate set, not a semantic partition. It must contain every registration that
Tree can select. BaseOnly may conservatively return additional registrations because several
distinct Tree exit branches and residual classes project to one packed access. In particular,
`emptyDeltaRequired` must not be used to discard a projected candidate when BaseOnly cannot prove
that every represented Tree branch belongs to the opposite class. The downstream residual/concat
operation is authoritative and rejects or specializes candidates after subscription delivery.

Registration deduplication remains exact. Candidate broadcast is therefore bounded by the
registrations for the selected method/base storage; it is not permission to cross caller endpoint,
callee base, or caller final base partitions.

### Z2F subscriptions

Logical registration key:

```text
(callee initial base, caller endpoint, caller final base, caller exit access)
```

Lookup emits a conservative candidate superset for the selected registration storage. Every Tree
`filterStartsWith` result must be present; the downstream residual operation remains authoritative.

### F2F subscriptions

Logical registration key:

```text
(callee initial base, caller endpoint, caller final base,
 caller initial fact including exclusions, caller exit access)
```

Lookup uses the shared candidate operation for both values of `emptyDeltaRequired`. Returned
builders preserve the exact registered caller initial fact and its exclusions. Tree currently
ignores the flag at this lookup boundary; BaseOnly may do the same because partitioning the merged
projection is unsound. The later residual operation still observes the requested analysis mode.

### ND subscriptions

Logical registration key:

```text
(callee initial base, caller endpoint, caller final base,
 canonical set of caller initial facts normalized to Universe exclusions,
 caller exit access)
```

Relevant-storage indexing must be complete for the candidate relation. Each selected registration
group may conservatively return all of its exits. `emptyDeltaRequired` has the same candidate-only
meaning as for F2F and must not remove a projected Tree match.

Tree comparison: Tree uses a final-access prefix index and `filterStartsWith`; Automata uses graph
localization plus `delta`/containment. BaseOnly may use its own index or scan the selected logical
registration group. Its emitted set must cover projected Tree matches; extra candidates are allowed
and are discharged by downstream residual processing.

## Publication and delta protocol

All SWMR stores follow this insertion protocol:

1. The writer canonicalizes and validates input without mutating shared state.
2. For each input, it computes the next persistent aggregate value.
3. It fully initializes a new leaf value or immutable replacement.
4. It publishes the leaf before or atomically with publishing its index key, according to the proven concurrent-read-safe collection protocol.
5. It updates secondary candidate indexes only with references to complete primary values.
6. It records the aggregate key in writer-local delta state.
7. After processing the batch, it reads the final persistent aggregate for each
   changed key, emits each required materialized component once, and clears
   writer-local delta state.

Readers resolve secondary entries back to the primary record and recheck the authoritative relation. A secondary index never becomes a source of truth.

Delta laws:

- inserting an already represented record emits no delta;
- reordering a batch does not change primary state or emitted logical delta set;
- splitting a batch may change when deltas are observed, but the union of emitted behavior equals the one-batch result;
- alias creation emits no delta;
- an exclusion-only update emits the committed aggregate, not a transient value;
- no delta is retained indefinitely after its batch is drained.

## Differential and reference laws

Every storage must be tested against a synchronized, scan-based reference implementation that stores canonical logical records directly and uses the definitions in this document. Tests compare denotations and logical keys, not iteration order.

For every bounded set of Tree records `T`, projection `project`, query `Q`, and BaseOnly result `B`:

```text
project(collectTree(T, Q)) ⊆ denotation(collectBaseOnly(project(T), project(Q)))
```

Required deterministic laws:

- duplicate insertion is idempotent;
- final state and logical deltas are insertion-order independent;
- all exclusion merge operators satisfy their declared algebra;
- candidate index plus authoritative filtering equals a full scan;
- identity and non-identity F2F storage implement the same edge denotation;
- distinct cross-slot identity records survive in both insertion orders;
- `Normal` and `Value` keys remain distinct through insertion,
  normalization, lookup, and joining; a join returns both facts in either
  insertion order;
- primary and normalized views share one exclusion value and aliases emit no deltas;
- each subscription mode returns a candidate superset of the corresponding Tree registrations;
- side-effect filtering never broadcasts a non-applicable same-base key;
- transient collapsed values have no observable effect;
- single-thread fact stores cover the corresponding Tree merged result.
- subscription registration before and after the analyzer makes summaries
  available returns the same conservative candidate language; subscriptions
  themselves remain analysis-thread-owned.

Required deterministic SWMR release schedules:

- read during first insertion;
- read during every index/table rehash;
- read between value initialization and key publication;
- read during exclusion aggregate replacement;
- two updates to one key in one writer batch;
- subsuming identity inserts in both orders;
- primary and normalized lookup overlap.

After the writer joins, collection must equal the reference state. During
writing, every observed record must belong to some complete committed prefix of
writer insertions; a reader may therefore observe an aggregate between two
inputs of the same writer batch. Batch boundaries govern delta draining, not
reader visibility.

The current tests establish the sequential laws above and exercise first-leaf,
rehash, and aggregate-replacement publication with concurrent stress loops. They
do not deterministically pause a reader at every publication boundary. Dedicated
scheduled tests are also still required for method Z2F, method ND,
fact-side-effect, and side-effect-requirement stores. Consequently, the semantic
storage operations may be Perfect below while the cross-cutting SWMR evidence
gate remains open; stress coverage alone is not proof of every required
interleaving.

## Per-storage conformance matrix

| Component | Ownership | Semantic reference | Required BaseOnly predicate/algebra |
|---|---|---|---|
| `BaseOnlyInitialAccessIndex` | SWMR when used by summaries | Tree `AccessBasedStorage.filterContains` | candidate superset, then `mayOverlap` |
| Intraprocedural Z2F set | single thread | Tree merged statement fact tree | exact/denotational set union |
| Intraprocedural F2F set | single thread | Tree per-initial statement store | exact initial; final union; exclusion union |
| Intraprocedural ND set | single thread | Tree per-initial-set merged tree | exact initial set; final union |
| `FinalFactList` | single thread | common/Tree list | exact LIFO tuple preservation |
| Method Z2F summaries | SWMR | Tree merging Z2F tree | final denotational union |
| Method F2F identity summaries | SWMR target; proof postponed | Tree identity trie | layered null-tombstone subsumption in the same slot; state-distinct suffix leaves; `mayOverlap` query |
| Method F2F non-identity summaries | SWMR | Tree per-initial merging store | `mayOverlap` query; exclusion intersection |
| Normalized F2F view | query-time SWMR read | Tree-resolvable backward match | primary-backed alias; no state/delta |
| Method ND summaries | SWMR | Tree initial-base index + merged finals | exact initial set; relevant-base completeness |
| Fact-side-effect summaries | SWMR | Tree filtered initial trie | `mayOverlap`; exclusion union |
| Side-effect requirements | SWMR | Tree `filterContains` | `mayOverlap`; exclusion union |
| Z2F subscriptions | analysis thread | Tree filtered caller-exit tree | conservative candidate superset; downstream residual authoritative |
| F2F subscriptions | analysis thread | Tree/Automata filtered caller exits | conservative candidates for either requested mode |
| ND subscriptions | analysis thread | Tree/Automata relevant-exit index | complete registration-group candidates |

## Mitigation verdict ledger

Verdicts are release gates, not statements about representation equality. **Perfect** means the
specification is general, the implementation follows it, and the cited bounded Tree differential
or storage law establishes that BaseOnly does not underapproximate the reference scenario.

| Component/API operation | Verdict | Tree-relative evidence |
|---|---|---|
| `BaseOnlyInitialAccessIndex.getOrCreate` / exact lookup | Perfect | `BaseOnlyInitialAccessIndexTest`; exhaustive value-accessor-state exact-key and duplicate laws |
| `BaseOnlyInitialAccessIndex.collectAll` / patterned candidates | Perfect | `BaseOnlyInitialAccessIndexTest`; `BaseOnlyF2FSummaryStorageLawTest.patterned query equals a scan-and-predicate reference` |
| Intraprocedural Z2F `add` / collect-all / patterned collect | Perfect | `BaseOnlyTreeDifferentialStorageTest.intraprocedural Z2F F2F and ND sets cover Tree collection and deltas`; `BaseOnlyFactSetTest` |
| Intraprocedural F2F collect-all / final-base pattern / exact-initial collect | Perfect | bounded differential scenario plus `BaseOnlyFactSetTest.f2f shares Tree fact-state exclusion union across its final language` and `f2f exclusion update retains Normal and Value finals separately` |
| Intraprocedural F2F `add` delta on exclusion-only aggregate change | Perfect | list-valued `MethodEdgesInitialToFinalApSet.add` re-emits every stored final with the merged exclusion; `MethodEdgesInitialToFinalApSetTest` covers Tree, Automata, Cactus, and BaseOnly, while `BaseOnlyFactSetTest` covers structural and Normal/Value final pairs plus publication through `MethodAnalyzerEdges` |
| Intraprocedural ND `add` / collect-all / final-base pattern / exact-initial-set collect | Perfect | bounded differential scenario plus `BaseOnlyFactSetTest.nd f2f canonicalizes initial exclusions before key publication` |
| `BaseOnlyFinalFactList.add` / `get` / `removeLast` | Perfect | Tree differential LIFO scenario plus rejected-transient/no-array-shift law in `BaseOnlyFactSetTest` |
| Method Z2F summary `add` / base-filtered and all-base collect | Perfect | `BaseOnlyTreeDifferentialStorageTest.method Z2F F2F and ND summary queries cover Tree`; duplicate/idempotence laws inherited from the exact set |
| Method F2F identity `add`, subsumption, merge, and delta | Perfect sequential semantics; SWMR evidence postponed | cross-slot, same-slot abstraction, exclusion, insertion-order, and value-state laws in `BaseOnlyF2FSummaryStorageLawTest` |
| Method F2F non-identity `add`, merge, and delta | Perfect | `BaseOnlyF2FSummaryStorageLawTest.nonidentity exclusion aggregation is intersection and insertion-order independent`; value-accessor-state key/candidate law; repeated-batch aggregate law; new-final/aggregate-exclusion publication stress coverage |
| Method F2F null-pattern and patterned collect | Perfect | `BaseOnlyF2FSummaryStorageLawTest.patterned query equals a scan-and-predicate reference`; bounded Tree F2F summary scenario |
| Method F2F normalized-view collect | Perfect | `BaseOnlyF2FSummaryStorageLawTest.normalized alias emits no delta and reads the primary exclusion`; alias/exact-primary dedup law |
| Method ND summary `add` / null-pattern and initial-base-pattern collect | Perfect | `BaseOnlyTreeDifferentialStorageTest.method Z2F F2F and ND summary queries cover Tree` |
| Fact-side-effect `add` / null-pattern and patterned collect | Perfect | `BaseOnlyTreeDifferentialStorageTest.fact side effects and requirements cover Tree filtering and exclusion union`; `BaseOnlyInitialAccessIndexTest` scan reference |
| Side-effect requirement `add` / collect-all / `filterTo` | Perfect | same bounded Tree differential scenario; `BaseOnlySubscriptionAndReqTest.side effect requirement filtering equals a scan reference` |
| Z2F subscription register / collect candidates | Perfect | `BaseOnlyTreeDifferentialStorageTest.Z2F F2F and ND subscriptions cover Tree residual modes`; candidate-superset law |
| F2F subscription register / empty and non-empty candidate collect | Perfect | same bounded differential scenario; `BaseOnlySubscriptionAndReqTest` conservative scan laws |
| ND subscription register / empty and non-empty candidate collect | Perfect | same bounded differential scenario; `BaseOnlySubscriptionAndReqTest` conservative scan laws |
| Cross-cutting SWMR publication evidence | Postponed known issue | current F2F/index stress tests do not deterministically force all required boundaries, identity null-tombstone publication has not been proven under every reader schedule, and dedicated concurrent-reader schedules are missing for Z2F, ND, fact-side-effect, and side-effect-requirement stores |

The differential suite intentionally compares bounded readable path languages instead of record
counts: Tree merges branches into access trees while BaseOnly may expose several records. Summary
stores and side-effect stores remain SWMR; the new differential scenarios are sequential reference
checks and therefore do not weaken or replace the deterministic concurrent-publication laws.

## Resolved representation/interface decisions

1. **Normalized-query control.** Resolved by the explicit one-way analyzer phase transition described above. A future common-interface query-mode parameter could make the phase local to a call, but is not required for correctness under the current forward-then-trace workload.
2. **Collapsed operational sentinel.** The access-domain specification permits it only in a
   transient final fact between `removeAbstraction` and `rebase`. Each BaseOnly insertion method
   rejects `access.isCollapsed` before calling or mutating its storage. Serialization validates
   the state directly. It is never a storage key or payload.
3. **Common-wrapper publication.** Common storage code is unchanged. Where a common wrapper would
   publish parallel metadata before the BaseOnly payload, the BaseOnly subtype overrides the
   public insertion method and rejects a collapsed access before delegating. BaseOnly otherwise
   uses the same confirmed concurrent-read-safe lazy wrappers as Tree/Automata.
4. **ND prefilter strength.** Base membership selects the logical registration group. ND
   subscriptions conservatively emit that group's exits for either mode; downstream residual
   processing is the authoritative filter.

These decisions do not waive Tree coverage, authoritative filtering, initialized publication, or no-delta alias requirements.

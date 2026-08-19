# BaseOnly summary-edge filter design

Date: 2026-07-20

## Goal

BaseOnly must return the same class of applicable summaries as Tree: for a non-null caller pattern `P`, return only summaries whose stored initial access `I` overlaps `P` by containment. Tree's `filterContains` returns both stored prefixes of an exact pattern and stored descendants of an abstract pattern. Today both BaseOnly fact-to-fact (F2F) and fact-side-effect (FactSE) storage ignore `P` and broadcast every summary for the selected fact base.

The filtering relation must be the existing AP operation, not a new approximation:

```kotlin
BaseOnlyAccessOps.containsAccess(P, I) || BaseOnlyAccessOps.containsAccess(I, P)
```

This is the BaseOnly equivalent of Tree's `filterContains(P)`. The two directions matter: an abstract caller pattern selects compatible stored descendants, while a stored abstract initial selects compatible concrete callers. Exclusions do not participate in index selection; they remain attached to the returned summary and are checked by the normal edge operations.

For `P == null`, collection remains an explicit full scan.

## Required behavior

For every F2F and FactSE query:

```text
applicable(P, I) = P == null || containsAccess(P, I) || containsAccess(I, P)
```

In particular:

- an exact pattern returns the exact initial and any initial prefix represented as compatible by `containsAccess`;
- an abstract static, field, or suffix slot can return all compatible descendants;
- a concrete field pattern can also match a stored `NO_ACCESSOR`, because BaseOnly field compatibility intentionally treats the missing field as compatible;
- a `NO_ACCESSOR` field in the pattern can match any stored field for the same reason;
- semantic suffix marks are compared by the existing suffix rule;
- exclusions never make an otherwise applicable initial key disappear.

Every indexed candidate should still pass the symmetric applicability predicate before emission. That final predicate is cheap and protects correctness if index routing is later changed.

## Storage layout

### Shared initial-access index

Introduce a small internal `BaseOnlyInitialAccessIndex<V>` keyed by the three packed access slots:

```text
static slot -> field slot -> suffix slot -> payload V
```

Each child table should use `ConcurrentReadSafeInt2ObjectMap`, the same single-writer/multiple-reader, eventually-consistent mechanism already proven by Tree. Payload publication follows the existing Tree approach. There are no removals.

The index exposes:

```kotlin
fun getOrCreate(access: BaseOnlyAccess, create: () -> V): V
fun collectAll(consume: (BaseOnlyAccess, V) -> Unit)
fun collectContainedBy(pattern: BaseOnlyAccess, consume: (BaseOnlyAccess, V) -> Unit)
```

`collectContainedBy` performs pattern-directed traversal. Slot routing mirrors the symmetric applicability predicate:

- `ABSTRACT_MARK`: traverse every child at that slot;
- concrete static: traverse only the identical static child;
- concrete field: traverse the identical field and `NO_ACCESSOR` children;
- field `NO_ACCESSOR`: traverse every field child;
- suffix `ABSTRACT_MARK`: traverse every suffix child;
- concrete suffix: traverse the identical suffix child;
- suffix `NO_ACCESSOR`: only the exactly equal access can match.

At each concrete pattern slot, the traversal also checks the stored abstract node at that slot; this is how an abstract identity such as `*` remains applicable to a concrete semantic fact. Early abstraction in the pattern can stop inspecting later slots exactly as `containsAccess` does. The final predicate check remains authoritative, so a conservative traversal may visit extra candidates but may not emit them.

### F2F non-identity edges

Replace `perInitial: Long2ObjectMap<MergingStorage>` with `BaseOnlyInitialAccessIndex<MergingStorage>`. A patterned lookup visits only compatible initial nodes and calls `MergingStorage.collectAll` for those nodes.

Keep each `MergingStorage.finals` in `ConcurrentReadSafeLong2ObjectMap`: one analysis thread writes while subscriber and trace threads may read. Delta lists stay ordinary single-thread-owned collections.

### F2F identity edges

The existing identity storage already has a three-layer static/field/suffix trie. Add pattern-directed `collectContainedBy` operations to its layers using the same routing rules, then guard each emitted initial access with the symmetric summary-applicability predicate.

Do not flatten identity summaries into the non-identity map: the identity trie performs exclusion intersection and subsumption while inserting, which must remain unchanged.

### Fact-side-effect edges

Replace `FactSESummariesBaseOnlyStorage.perInitial` with the shared initial-access index. Patterned collection visits only compatible initial nodes and emits that node's merged side effects. `SideEffectExclusionMergingStorage` already uses `ConcurrentHashMap` for the inner side-effect-kind map and needs no fact-set-related change.

### Normalized F2F aliases

Keep normalized aliases collection-only:

- `trackDelta = false` for the entire normalized storage;
- never allocate or retain normalized delta lists;
- query the normalized index with the same caller pattern instead of scanning it;
- enable normalized lookup only in the existing trace-resolution phase;
- deduplicate exact `(initial access, final access, exclusion)` results across primary and normalized storage before building edges.

Normalization can intentionally produce a different initial access and therefore a distinct trace alternative. Such alternatives must not be deduplicated merely because their final access is equal.

## Concurrency contract

The storage contract remains:

```text
one writer, multiple concurrent readers, eventually consistent
```

Consequently:

- shared indexes and shared final maps use concurrent-read-safe tables;
- readers may miss an insertion concurrent with their current traversal, but a later query observes it;
- readers must never use live fastutil iterators over a table that can rehash;
- no locking or snapshot copying is required;
- ordinary IFDS fact sets and delta collections remain single-threaded and should not be replaced with concurrent collections.

This matches the confirmed Tree/Automata workload rather than strengthening the contract unnecessarily.

## Safe implementation sequence

1. Add a scan-and-predicate implementation first: retain the current indexes but emit only entries satisfying the symmetric applicability predicate. This is the executable correctness oracle and immediately removes unrelated summaries, although lookup remains O(number of initials).
2. Add the shared trie index and run every filter test against both implementations.
3. Switch F2F non-identity and FactSE storage to the trie.
4. Add pattern-directed identity traversal.
5. Add normalized-store filtering and exact-result deduplication.
6. Remove the scan reference only after differential and E2E verification.

## Verification plan

### Deterministic semantics

Pin F2F and FactSE cases for:

- exact pattern versus same and different initial access;
- abstract pattern versus concrete descendants;
- concrete field versus stored `NO_ACCESSOR`;
- pattern `NO_ACCESSOR` versus stored concrete field;
- concrete and abstract suffixes, including semantic marks;
- static-access equality and static abstraction;
- null pattern returning all summaries;
- exclusions changing the returned edge but not index applicability;
- identity and non-identity summaries obeying the same filter;
- normalized aliases available only when enabled, with no delta and no exact duplicate.

### Differential oracle

Generate random packed accesses, insert them into the scan reference and trie, and for every generated pattern compare the exact emitted key set. Compute the expected set directly with the symmetric applicability predicate. Also compare representative BaseOnly results with Tree `filterContains` after constructing equivalent APs.

### Concurrency

Run one writer through enough distinct slot keys and finals to force repeated rehashes while several readers issue exact, abstract, and full-scan queries. Assert no exception or malformed edge, then join the writer and assert eventual completeness. Cover primary F2F, normalized F2F, identity F2F, and FactSE storage.

### Performance gates

Instrument and assert structural work rather than wall-clock time:

- initial index nodes visited;
- candidate initial keys checked;
- summaries emitted per patterned lookup;
- primary and normalized duplicates removed;
- downstream summary applications per analysis unit.

A query with one compatible initial among many incompatible initials must emit one and should visit only the compatible trie branches. E2E acceptance should include the previously explosive Apollo, Klaw, OpenMRS, and TMS methods and require complete analyzer status before comparing findings.

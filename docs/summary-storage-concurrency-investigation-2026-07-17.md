# Summary storage concurrency investigation

Date: 2026-07-17

## Result

The summary storage contract is single-writer/multiple-reader. BaseOnly violates that contract by iterating ordinary mutable fastutil maps while the writer may insert and rehash them. This is the direct cause of the four incomplete BaseOnly E2E runs.

Tree and Automata already use concurrent-read-safe, eventually-consistent indexes and captured-size/table traversal. These approaches are confirmed safe under the analyzer workload and are the implementation model for BaseOnly. BaseOnly should use equivalent primitive-long structures at every summary index that can be read while its single writer adds entries.

Ordinary IFDS fact sets are different: they are owned and used by one analysis thread. They do not need concurrent-read-safe replacements. The scope of this fix is summary storage and other explicitly shared indexes, not every fastutil collection used by BaseOnly.

## Actual concurrency boundary

`SummaryEdgeStorageWithSubscribers` serializes these writes with `synchronized(storage)`:

- zero-to-fact summaries: `SummaryEdgeSubscription.kt:866-872`
- fact-to-fact summaries: `SummaryEdgeSubscription.kt:884-890`
- non-distributive fact-to-fact summaries: `SummaryEdgeSubscription.kt:898-904`
- fact side-effect summaries: `SummaryEdgeSubscription.kt:848-850`

Queries at `SummaryEdgeSubscription.kt:918-988` do not take the same monitor. Therefore the monitor ensures one effective writer for each storage, but creates no happens-before edge for readers and does not prevent read/write overlap.

The common layer also publishes mutable state without a complete synchronization protocol:

- `SummaryFactStorage.locals` and `constants` are lazily assigned non-volatile references to `ConcurrentHashMap`s (`SummaryEdgeSubscription.kt:1093-1124`).
- `AccessPathBaseStorage` keeps `this`, `return`, `exception`, static, and argument slots in plain fields/array elements (`AccessPathBaseStorage.kt:5-69`).
- exit points and their storages are parallel mutable `ArrayList`s (`SummaryEdgeSubscription.kt:1143-1181`). Indexed traversal snapshots the list size, but does not safely publish the elements (`ListUtils.kt:13-38`).

## Proven BaseOnly failures

### Fact-to-fact summaries

`MethodInitialToFinalBaseOnlyApSummariesStorage.F2FStorage` uses:

```text
perInitial: Long2ObjectOpenHashMap<MergingStorage>       line 28
writer:     getOrCreate/put                              line 60
reader:     perInitial.values.forEach                    line 72
```

The nested `MergingStorage` repeats the same unsupported pattern:

```text
finals: Long2ObjectOpenHashMap<ExclusionSet>             line 299
writer: get/put                                          lines 303-317
reader: finals.forEach                                   lines 329-332
```

The normalized F2F alias is another recursively constructed `F2FStorage`, so it contains the same two races (`MethodInitialToFinalBaseOnlyApSummariesStorage.kt:21-28,74-76`).

Conductor and TMS crashed in the outer `perInitial.values` iterator:

- `run-debug/result-conductor-new/analyzer.log:5592-5602`
- `run-debug/result-tms-new/analyzer.log:2568-2578`

Both stacks end in:

```text
Long2ObjectOpenHashMap$MapIterator.nextEntry
Long2ObjectOpenHashMap$ValueIterator.next
MethodInitialToFinalBaseOnlyApSummariesStorage$F2FStorage.collectSummariesTo
```

The exception says the iterator's `wrapped` `LongArrayList` is null. A fastutil open-hash iterator snapshots iteration counters but walks the live table. An overlapping insert/rehash can make the iterator exhaust its visible table before its saved count, sending it into the wrapped-key path even though no wrapped list was created. One writer and one reader are sufficient; no concurrent writers or removals are required.

### Fact side-effect summaries

`FactSESummariesBaseOnlyStorage.SEStorage` has the same outer-map defect:

```text
perInitial: Long2ObjectOpenHashMap<MergeStorage>          line 17
writer:     get/put                                      line 24
reader:     perInitial.values.forEach                    line 34
```

Apollo and Klaw crashed in this iterator:

- `run-debug/result-apollo-new/analyzer.log:2832-2842`
- `run-debug/result-klaw-new/analyzer.log:2420-2430`

The per-initial side-effect values inherit `SideEffectExclusionMergingStorage`, whose kind map is a `ConcurrentHashMap`; that safe inner map does not make the unsafe outer `Long2ObjectOpenHashMap` iterable.

### Other BaseOnly stores with the same risk

These did not cause the four saved stacks, but also expose ordinary fastutil collections to overlapping reads and writes:

| storage | mutable structure | read/write locations |
|---|---|---|
| zero-to-fact | `LongOpenHashSet` | `MethodFinalBaseOnlyApSummariesStorage.kt:14-24` |
| ND fact-to-fact | `LongOpenHashSet` | `MethodNDInitialToFinalBaseOnlyApSummariesStorage.kt:32-49` |
| side-effect requirements | nested `Long2ObjectOpenHashMap` | `BaseOnlySideEffectRequirementApStorage.kt:27-49` |
| F2F identity trie | mutable nodes plus custom int maps | `MethodInitialToFinalBaseOnlyApSummariesStorage.kt:79-291` |

The two observed iterator sites must be fixed first, but treating only those stack frames would leave the same contract violation elsewhere.

## Tree storage

Tree's primary initial-access index is a trie (`AccessBasedStorage`):

- child maps use `ConcurrentReadSafeInt2ObjectMap` (`AccessBasedStorage.kt:15`);
- point reads use a custom rehash-tolerant `get` (`ConcurrentReadSafeInt2ObjectMap.java:8-46`);
- traversal uses `forEachEntry`, which captures key/value arrays and retries if their sizes disagree with the captured table size (`MapUtils.kt:8-33`);
- final access-tree nodes are immutable (`AccessTree.kt:238-245`);
- merged summary updates construct a replacement access-tree root (`MergingTreeSummaryStorage.kt:15-44`);
- side-effect kind/exclusion merging uses `ConcurrentHashMap` (`CommonFactSideEffectSummary.kt:85-106`).

This avoids the exact live fastutil iterator that crashes BaseOnly and makes readers consume mostly immutable access-tree roots. It provides the analyzer's intended eventually-consistent reader semantics and is confirmed safe under current workloads.

## Automata storage

Automata also uses concurrency-aware outer indexes:

- F2F initial graph lookup uses `ConcurrentReadSafeObject2IntMap` (`MethodInitialToFinalAutomataApSummariesStorage.kt:22`).
- initial graphs and final stores are parallel append-only arrays traversed with an indexed size snapshot (`MethodInitialToFinalAutomataApSummariesStorage.kt:23-24,53-81`).
- side-effect initials use `ConcurrentHashMap` (`FactSESummariesAutomataStorage.kt:18-39`).
- access-graph groups have a `ConcurrentHashMap` outer index (`AccessGraphStorageWithCompression.kt:6-45`).

Its inner state is mutable and read with the same one-writer/eventually-consistent contract:

- `AgGroup` mutates roots, an ordinary delta list, and an `AccessGraphSet` (`AccessGraphStorageWithCompression.kt:59-122`).
- `SmallAgSet` and `CompressedAgSet` mutate ordinary fastutil sets/maps that readers enumerate (`AccessGraphSet.kt:151-251`).
- `GraphIndex` mutates ordinary `BitSet`s and nested custom maps while queries read them (`GraphIndex.kt:9-212`).

Automata's append-only indexed traversal and concurrency-aware outer indexes are also confirmed safe under current analyzer workloads. BaseOnly can copy these access patterns while retaining its packed primitive representation.

## Separate BaseOnly performance issue

BaseOnly F2F collection ignores the supplied `initialFactPattern` and always emits every identity and per-initial summary (`MethodInitialToFinalBaseOnlyApSummariesStorage.kt:67-76`). Tree filters its trie with the pattern (`MethodInitialToFinalApSummaries.kt:234-253`), and Automata localizes compatible initial graphs (`MethodInitialToFinalAutomataApSummariesStorage.kt:62-98`).

BaseOnly fact-side-effect storage also ignores its pattern (`FactSESummariesBaseOnlyStorage.kt:30-35`). This is sound as an overapproximation, but applies unrelated summaries at every call and can multiply forward candidates and trace work. It is a plausible contributor to the Stirling/OpenMRS/HertzBeat code-flow and trace-time expansion documented in the E2E report.

BaseOnly should filter initial keys using its containment/field-compatibility semantics, including normalized aliases. This optimization needs differential correctness tests because an over-restrictive filter would create forward misses.

### Normalized-summary delta leak

Normalized F2F aliases have a separate concrete memory bug. The outer store inserts an alias through the private `normalizedStorage.add(..., modified = null)` path (`MethodInitialToFinalBaseOnlyApSummariesStorage.kt:38-44`). That path bypasses the public batch add's delta drains (`:47-48`), but `MergingStorage.add` still appends each change to `deltaFinals` and `deltaExclusions` (`:300-316`). Identity aliases similarly leave `LayerBase.delta` allocated. The normalized store exists only for collection, so those delta lists are never consumed and grow for the method storage's lifetime.

The fact that aliases are inserted while `normalizedEdgesEnabled()` is false is intentional: `TaintAnalyzer.kt:210-216` enables them only after forward analysis, before trace generation. The aliases must therefore be accumulated during the forward phase. The implemented design makes the normalized store explicitly collection-only and threads `trackDelta = false` through identity and merging additions. Draining into a scratch builder list would stop retention but needlessly allocate objects.

## Fix proposal

### 1. BaseOnly implementation

Add primitive-long equivalents of the proven Tree collections:

- `ConcurrentReadSafeLong2ObjectMap` provides rehash-tolerant point lookup by capturing a matching key/value table generation;
- its `forEachEntry` captures the key array, value array, and table size, retrying when they belong to different rehash generations;
- `ConcurrentReadSafeLongSet` and `forEachLong` apply the same scheme to packed summary sets;
- removals are forbidden; updates remain single-writer and readers are intentionally eventually consistent.

Use these structures in both outer and nested shared indexes: F2F `perInitial`, F2F `finals`, fact side-effect `perInitial`, zero-to-fact summaries, ND summaries, and shared side-effect requirements. Keep delta collections and ordinary IFDS fact sets unchanged because their use is single-threaded.

This preserves BaseOnly's unboxed representation and the non-blocking read behavior already used by Tree/Automata. A boxed `ConcurrentHashMap<Long, ...>` or a storage-wide read/write lock is unnecessary for the confirmed workload.

### 2. Optional stronger snapshot model

If the concurrency contract later expands beyond one writer or requires point-in-time consistency, publish immutable snapshots at the end of each add batch through `@Volatile` roots. That is a different, stronger contract and is not required for the current eventually-consistent workload.

### 3. Verification

Add deterministic stress tests at the public storage boundary:

1. one writer repeatedly adds F2F edges with enough distinct packed accesses to force rehashes while several readers call `factEdges` and full-summary collection;
2. the same pattern for fact side-effect summaries;
3. zero-to-fact, ND F2F, and side-effect-requirement variants;
4. assert no exception, no malformed builder, and eventual completeness after the writer joins;
5. run the same suite for Tree, Automata, and BaseOnly.

After the correctness fix, rerun Apollo, Conductor, Klaw, and TMS. Their current result counts cannot be treated as semantic comparisons because the scans terminated at these iterator failures.

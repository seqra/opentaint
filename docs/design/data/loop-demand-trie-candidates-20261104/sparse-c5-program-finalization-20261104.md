# Candidate: sparse prepared-C5 program finalization

4 November 2026. **UNSELECTED PROPOSAL ONLY. No Kotlin changes or experiment.**
Source examined: runtime `52f32dd437d438aec4a700a02c18d94c31d58093`.

## 1. Exact source cost

`PreparedOutputPrograms.intersect` currently:

1. Allocates `arrayOfNulls<ProgramBucket>(programs.size)` at line 35.
2. Enumerates native protected/ordinary scalar streams once, queries the output
   trie, and creates a ProgramBucket only after a non-null native selection
   (lines 38–59, particularly line 47).
3. Rejects the whole attempt on reference-budget overflow before returning output
   (lines 62–63).
4. Visits **every** immutable output program at lines 65–89. A missing bucket
   performs cancellation/diagnostic work and emits no AP result. Only a present
   bucket calls native packing, mask attachment and field limiting.

Let s be this plan's output-program count, k the number of buckets actually
created for this query, chi the scalar/program candidate count, and u the number
of unique selected `(program, stream, Conclusion)` references. Successful queries
have `k <= min(s,u) <= 2048`. The existing preparation cap also bounds s, but it
still incurs an s-sized reference array and s program visits for every query.

**The current implementation already allocates ProgramBucket and its two sets
only for selected programs.** This candidate does not reduce that object count,
selected native restrictions, selected packs, protection transport or field cuts.
It removes the dense reference array/zeroing and the empty-program scan.

## 2. Proposed query-only representation

Use a lazily created private sparse container:

```kotlin
private class SelectedPrograms {
    val buckets = Int2ObjectOpenHashMap<ProgramBucket>()
    val ordinals = IntArrayList()

    fun getOrCreate(ordinal: Int): ProgramBucket = buckets[ordinal]
        ?: ProgramBucket().also {
            buckets.put(ordinal, it)
            ordinals.add(ordinal) // only the first creation of this exact key
        }
}
```

The actual get operation must distinguish a missing entry from its non-null
ProgramBucket; do not use a null sentinel as an empty selected bucket.

```text
selected = null
references = 0

for each existing native protected-first scalar:
    for each existing trie program candidate:
        conclusion = unchanged restrictConclusionOnly(...)
        if conclusion == null: continue
        bucket = (selected ?: allocate SelectedPrograms).getOrCreate(ordinal)
        if bucket.stream.add(conclusion):
            references++
            if references > 2048: discard query; return native-fallback sentinel

# No ordinary result has escaped before this check.
if selected == null: return exact empty list
sort selected.ordinals numerically ascending

for ordinal in selected.ordinals:
    program = programs[ordinal]
    bucket = selected.buckets.get(ordinal)
    for packet in unchanged packProgramStreams(bucket):
        unchanged native limit(packet, program.budget) -> ExactDemandResults
return ExactDemandResults.all()
```

Keep both ordered LinkedHashSet streams in each bucket. Create the bucket only
after native selection succeeds. Never append an ordinal on duplicate selections.
A bucket can have protected selections even if the eventual native pack emits
nothing; select by actual bucket presence, not a guessed nonempty output.

Sort by the immutable **program ordinal**, not original row ID, hash-table order
or input discovery order. Program ordinal already denotes first accepted native
member -> prefix -> row order. For example, scalar enumeration can first find
program 2 at `.a` and then program 0 at `.b`. Finalizing `[2,0]` would reverse the
native output stream. The correct sparse finalization remains `[0,2]`.

An existing primitive merge-sort implementation can give O(k log k) sorting with
O(k) auxiliary space. Sorting a primitive key array avoids boxed key objects.
Its ordering is solely natural Int order; no AP matching occurs in the comparator.
Keep checkpoints before/after the bounded sort and during the selected loop.

## 3. What remains exactly the same

- Entry preparation, every paired eligibility check, whole normalized P and
  first-accepted program grouping are unchanged.
- Scalar stream order, each stream's header, trie candidates and native selection
  are unchanged. Full marks, E/Mx, exact/uniform tails and protection stay intact.
- The unique-reference counter and 2,048 threshold are unchanged. On overflow,
  return null and recompute the **whole** native C5 query; return no partial result.
- For each selected program, use the same native `packProgramStreams`, which packs
  the protected stream, records masks, packs the ordinary stream and attaches
  those masks (`DemandScalarStreams.kt` lines 35–43).
- Apply the existing program field limit **after** whole-program packing, then
  add results in native program order to the same exact annotated union.
- Keep run-1/Zero/static/run-2/unsupported factory and query fallbacks unchanged.
- Keep normal/demand layers, all scoped ports and publication keys unchanged.
- These are query-local buckets. Do not retain them in a plan or scratch cache,
  and do not add their identities to Facts, Pattern, Record or summary equality.

No rule, source permission, subscription, request, Target, actual AP transfer,
completion or route policy changes. The replacement is not an excuse to skip a
selected program whose nonempty native output looks redundant.

## 4. Cost and retention

Current query overhead, apart from shared native selection/pack/limit costs:

```text
Theta(s) reference array initialization + O(chi) direct bucket lookups + Theta(s) scan
```

Sparse query overhead:

```text
expected O(chi) primitive hash lookups + O(k log k) sorting + Theta(k) scan
```

Query-local bucket-container retention changes from O(s+k+u) to O(k+u), with k=0
allocating neither container. The existing program plan and accepted tickets are
still retained as before; this does not shrink them. Overflow can transiently
contain the first 2,049th reference before immediate disposal, as it does now.

Sparse maps/key arrays have larger per-selected-entry overhead than one dense
array slot. When k is close to s, hashing and sorting can cost more than the dense
version. No hybrid threshold is selected by this note. Need actual per-query
s/k occupancy and allocation attribution before claiming an overall benefit.

## 5. Diagnostics change must be explicit

The existing dense loop counts every program visit, including missing buckets,
in legacy `c5Candidates`, `c5Restrict`, `c5RowAttempts` and rejection/sample work.
Sparse execution no longer performs those missing-bucket visits. It cannot keep
the old per-program empty-row samples, per-Dp histogram events or sample-ordinal
schedule without reintroducing the s scan.

Preserve the old keys for compatible parsers, but document their measured work
meaning. Add O(1) bulk census counters only after the existing output-base guard
has passed and selection completes without reference overflow (exactly where the
old dense finalizer would run):

```text
c5PotentialProgramVisits += s
c5SelectedProgramFinalizations += k
c5EmptyProgramVisitsAvoided += s-k
```

An output-base early return already avoids the dense array/scan today; count no
new saved visits there. An overflowing attempt already returns before the dense
scan, so count no saved finalizer visits there either. A separate dense-bucket-slot
allocation counter can count s immediately after the base guard, including the
attempts that later overflow, because the old array allocation precedes selection.

New per-row samples describe selected program finalizations. A bulk skipped count
can replace the old rejected-row count if that numeric definition is useful; do
not fabricate individual rejected-row trace events. Native limit calls/results,
stream/scalar enumeration, candidate callbacks and unique-reference definitions
remain the same for a fixed query input.

The currently logged prepared `c5StreamPacks` gives only a bound on total selected
finalizations: each occupied bucket causes one ordinary pack and at most one
protected pack. Thus `ceil(packs/2) <= selectedFinalizations <= packs`, not an exact
k. Legacy c5RowAttempts mixes native rows and dense prepared-program visits, so a
population density cannot be inferred by simply dividing the two counters.

## 6. Conditional constructive model and native gate

The companion `sparse-c5-program-finalization-20261104/Sparse.lean` models full
ordered opaque selection streams, annotated output payloads and deterministic
native pack/limit emission. It proves:

- empty cells contribute no output;
- sorting a sparse key permutation restores the original ascending plan order;
- the entire ordered annotated output stream equals dense finalization;
- the same final annotation-aware union receives identical input;
- selected finalizers are bounded by s, and by the reference cap when each bucket
  owns at least one counted reference;
- overflow returns native fallback without partial output;
- missing/duplicate keys reject an executable reference certificate;
- unsorted encounter order is an explicit counterexample.

The model does not prove the Kotlin int-map implementation or the native AP
packer. Native obligations are exact sparse key support/uniqueness, bucket stream
identity, valid ordinals and unchanged emitter. The executable dense certificate
belongs in tests, not the hot path.

Required native controls before implementation:

1. Large s, zero or one occupied bucket: same ordered annotated result and no
   dense bucket array/all-program finalizer. Use an explicit diagnostic work seam.
2. Encounter `[later,earlier]` ordinals, duplicate candidates and duplicate selected
   conclusions: first-program output order and full exact union remain native.
3. Protected exact plus uniform E sibling: same independent headers/masks and
   pack-before-limit behavior as current tests.
4. Exactly 2,048 refs succeeds; 2,049 returns null before output; whole native
   fallback reproduces the old result, not only the selected prefix.
5. Complete ND original/ports, FLOW exclusions, multi-mark packets, reverse/MUST
   callers and run-2/static fallback remain native-equivalent.
6. Cancellation before/during sorting/finalizing publishes no partial answer and
   retains no sparse query container.
7. Pin diagnostics definitions; do not compare changed rejected-sample counts as
   evidence of changed AP results.

## 7. Evidence and priority limits

Parent-reported run-6 counters (39.8m streams, 48m scalars, 107m candidates) and
11.28% Java program-selection bookkeeping motivate examination, not a speedup
estimate. That classifier includes work this change cannot avoid. Existing source
lines prove the dense allocation/scan; exact selected occupancy and allocation
class/call-site evidence remain needed.

The separate exact-scalar memo remains only a future conditional candidate.
The new early 0.304s trace sample had 339 growing frames and 339 distinct full
keys; its 393 observations also had 393 distinct keys, giving zero unbounded
exact-key hits in that sample. Do not promote memoization from this evidence or
turn the sample into a global hit-rate claim. Sparse finalization removes a cost
within each query and does not require repeated complete query keys.

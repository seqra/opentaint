# Implementation proposal: P3 and P2' of the next iteration

Status: IMPLEMENTED, 25 November 2026. P3 is landed (`0919c7500`). P2' was
landed (`ad7b06320`) and reverted (`c89881544`) by the memory clause of
§6.3: the landing measurement kept all results, but the memo added
0.8-1.4 GB to the heap after GC of the long loop runs (Conductor runs 6-8,
Stirling-PDF stall runs) and 70% to the GC pause time of Conductor
([landing report](../docs/reports/bidirectional-p3-p2m-landing-20261125.md)).
The next proposal (N4 of
[bidirectional-next-iteration-20261126.md](../docs/design/bidirectional-next-iteration-20261126.md))
bounds the memo footprint. Proposal date: 25 November 2026. Base: `saloed/bidirectional` at
`29c78d5c3`. Its core is identical to `c5702ba4f` and to the measured
group A core `5804e44dd`, so the prototype gates of the spec apply to
this base. This proposal follows
[impl-proposal-guide.md](impl-proposal-guide.md),
[proof-guide.md](proof-guide.md) and [design-guide.md](design-guide.md).

- Source spec: [next-iteration-p1-p3.md](next-iteration-p1-p3.md):
  - §0, the classification: P3 and P2' are WI;
  - §2, P3;
  - §3.6, P2';
  - §5, plan items 1, 2 and 5.
- Prototype branch: `proto/p1-p3-20261125`. P3 is in `2ad12e049`, and
  P2' is in `f3910bede`.
- Proofs, in `spec/lean/ApSpec/`:

  | Module | Level | Theorems |
  | --- | --- | --- |
  | `FlowGroupIncremental.lean` | P3 rule (spec §2.4) | 11 |
  | `FlowGroupIncrementalImpl.lean` | P3 implementation (§3.4) | 7 |
  | `RestrictionMemo.lean` | P2' rule (spec §3.6) | 4 |
  | `RestrictionMemoImpl.lean` | P2' implementation (§4.4) | 5 |

  Check: `cd spec/lean && lake build && lake env lean audit.lean`. The
  audit gives 46,038 declarations and 0 unexpected axioms. Only
  `propext` and `Quot.sound` occur.

Line numbers refer to `29c78d5c3`. File paths are relative to
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/bidi/`.
`test:` means
`core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/`.

## 0. Summary

| Id | Rule | Where it acts | What changes | Proof |
| --- | --- | --- | --- | --- |
| P3 | Incremental canonicalization in `FlowGroup.addAll` | `ap/Groups.kt`, every FLOW store, all runs | An insert that changes no row returns at once. A pass subtracts a clean row only by the changed rows. The native final pass is deleted. A call that throws restores its list | `FlowGroupIncremental.lean`, `FlowGroupIncrementalImpl.lean` |
| P2' | Per-run memo of the loop-output restriction | `engine/MethodBlockRuntime.kt` `onApplied`, new `engine/LoopRestrictionMemo.kt`, runs ≥ 2 | A method runtime computes the restriction of one key once per run, while the memo is not cleared | `RestrictionMemo.lean`, `RestrictionMemoImpl.lean` |

Both rules are exact. They change no result, no stored value and no
returned delta. They change only the work. The landed code has no
switch, no census and no counter.

Not in this proposal: P2'' (the order of the loop-block worklist) and
P1. The spec has no rule for them yet (spec §5, items 3 and 4).

## 1. Decisions that this proposal implements

| Date | Decision | Effect here |
| --- | --- | --- |
| 24 Nov | No switch and no in-code census: this is the implementation, not a prototype | §3.3, §4.3: do not take `Proto.kt`, the `SHADOW` branches or the counters |
| 24 Nov | Never relax the FL+1 caps | Not touched: P3 and P2' make no deeper fact and no new fact (§2) |
| 24 Nov | Serve every route | Not touched: both rules keep every stored value and every delta (§2) |
| 24 Nov | Single launch per measurement; more only if the numbers are not representative | §6.2. Stirling-PDF gets three launches, because its stall depends on the order of work (spec §1) |
| 24 Nov | The whole analyzer is measured after the implementation lands | §6.2 |
| 25 Nov | P3 is WI; P2' is WI, and the landing gate repeats OWASP on a quiet host (spec §0) | §6.2 |
| 25 Nov | P3 and P2' go into the next iteration | This proposal |

The proposal makes six calls of its own (§8). No question is open.

## 2. Semantic scope

**Changed.** Nothing that the analysis can see:

- P3 changes the work of one `FlowGroup.addAll` call. The stored rows,
  their order and the returned delta are the native ones (§3.4).
- P2' changes the work of one restricted loop output. The returned list
  is the native one (§4.4).

**Unchanged.** Field transfer, premise matching, layers, sources and
sinks, marks, the FL+1 caps, `TaintGroup`, the T1-T4 merge rules, the
MUST merge, the promotion rule, the restriction rule (baseline, budget
trials, C2/C5 queries), the loop blocks, the stores, the hand-off, the
demand and the reports.

**Data-class equality and hashing.** No stored value changes its
equality or its hash. P2' adds one key class,
`LoopRestrictionMemo.Key`. It is not stored in an analysis store, and it
takes no part in the deduplication of facts. Its equality uses the
structural `Facts` equality, which compares every field, the layer and
the protection included (`ap/Conclusions.kt:37-38`, `:62-64`).

**Behavior on a throw (P3).** Native leaves a partial list when a
cancellation interrupts `addAll`. P3 restores the list that the call
read (§3.3 (d)). Native also gives this list when the cancellation hits
the first checkpoint of `insert` (`ap/Groups.kt:18`), so the restored
state is a state that native can reach. The restore keeps the invariant
of §3.1 for every later reader.

**Diagnostics (P2').** A memo hit does not call `restrict`. Thus the
existing diagnostic counters `restriction.statistics` and `queryCounts`
(`MethodBlockRuntime.diagnosticStatistics`) and the debug trace record
`loop-observation` count only the computed restrictions. The results do
not change.

## 3. P3: incremental canonicalization in `FlowGroup.addAll`

### 3.1 Definition

A `FlowGroup` holds two lists of rows, one per layer. A pass (`pass`)
replaces each row `r` by `compactPacket(r)` minus the covers of all
other rows. An empty row goes. The MUST merge is `mergeMustOverlap`, and
the promotion is the promotion scan.

**Invariant F.** Between two calls, each list is a fixpoint: a pass, the
MUST merge and the promotion change nothing.

```text
addAll(t):                                   // landed form
  before = copy(list)
  try:
    insert(t)
    if list has the same row objects as before: return []           // (a)
    clean = before
    loop:
      dirty = rows of list that are not objects of clean
      list  = [ r in clean ? subtractSubsumed(r, dirty)                // (b)
                           : subtractSubsumed(compactPacket(r), list − r)
                for r in list ]
      clean = list
      if mergeMustOverlap(list): continue
      p = promotion(list); if p == null: break
      insert(p)
    return [ r − (roots of before with the group key of r) for r in list ]   // (c) no final pass
  on any throw:
    list = before; rethrow                                               // (d)
```

- (a) P3 tests the row objects, not the return value of `insert`.
  `insert` can return null after it removes a row (`ap/Groups.kt:42`),
  and it returns a value only when it changes the list.
- (b) A clean row is a row object of the stored list, or of the last
  pass output, that no merge and no insert replaced.
- (c) The native final pass is deleted. The loop ends right after a
  pass, so the final pass changes nothing (`final_pass_noop`).
- (d) A call that throws has no effect on the list.

### 3.2 Native code

| Site | Lines | Behavior |
| --- | --- | --- |
| `ap/Groups.kt` `class FlowGroup`, `trees` | 8-9 | Two private lists. Only `insert`, `addAll` and `mergeMustOverlap` write them. No restore and no bulk load |
| `insert` | 14-51 | T1/T2/T2'/T4. Changes the list in place. Every checkpoint comes before the first write of a loop step |
| `add` | 53-55 | `addAll` plus a size check. Not changed |
| `addAll` | 57-109 | Insert (result ignored); loop: full pass (64-67), merge (68), promotion scan (69-90), insert (92); final full pass (94-99); delta (100-108) |
| `mergeMustOverlap` | 111-130 | Replaces two rows by new objects and inserts the merged row |
| `compactPacket` | 132-151 | Returns the same object when no position is covered |
| `subtractSubsumed` | 152-171 | Subtracts the covers of the given rows (`FlowAlgebra.subtract`, `ap/TrieOps.kt`) |
| `ConclusionGroup.addAll` / `add` | 367-382 | The only production callers. They create a `FlowGroup` empty |

### 3.3 Code changes

Take the logic of `addAllIncremental` and `promotion` from `2ad12e049`
(`ap/Groups.kt` on the prototype branch). Do not take the
`Proto.Mode` parameter, `addAllNative`, the `SHADOW` branch, the
counters, `Proto.kt`, `ProtoFlagsEchoTest`, the `IterationDriver` drain
line or the harness option `--jvm-prop`.

**(a) State invariant F at the field.**

```kotlin
/** FLOW values for one base, separated by layer and both exclusions. One store writer owns this group.
 *
 * Invariant F: between two calls, each list of [trees] is a fixpoint. A pass, the MUST merge and the
 * promotion change nothing in it. The list starts empty, only [addAll] (through [insert] and
 * [mergeMustOverlap]) writes it, and [addAll] stores a fixpoint or restores the list that it read.
 * [addAll] needs F for its early return and for its clean rows (spec/next-iteration-p3-p2m-implementation.md §3).
 * A new writer of [trees] must keep F. */
class FlowGroup(private val m: ApManager, private val interner: TrieInterner<FlowLeaf>) {
```

**(b) `addAll`.** Replace lines 57-109:

```kotlin
fun addAll(t: FlowTree): List<FlowTree> {
    val list = trees[t.layer.ordinal]
    val before = list.toList()
    try {
        insert(t)
        // F: `before` is a fixpoint. When the insert keeps the same row objects, nothing changes.
        if (sameRows(list, before)) return emptyList()
        canonicalize(list, before)
        return list.mapNotNull { row -> newPart(row, before) }
    } catch (e: Throwable) {
        // A throw (a cancellation) keeps F: restore the list that this call read.
        list.clear(); list.addAll(before)
        throw e
    }
}

private fun sameRows(a: List<FlowTree>, b: List<FlowTree>): Boolean =
    a.size == b.size && a.indices.all { a[it] === b[it] }
```

**(c) The loop, with clean rows and no final pass.**

```kotlin
/** The native loop of passes, MUST merges and promotions. A row that is still an object of [clean]
 * (the stored fixpoint, then the last pass output) is compact, and no other clean row covers it.
 * So only the changed rows can cover it. The loop ends after a pass, so the native final pass
 * changed nothing and is deleted (Lean `final_pass_noop`, `addAllImpl_eq`). */
private fun canonicalize(list: MutableList<FlowTree>, clean: List<FlowTree>) {
    var cleanRows = clean
    while (true) {
        val dirty = list.filter { row -> cleanRows.none { it === row } }
        val canonical = list.mapNotNull { row ->
            if (cleanRows.any { it === row }) subtractSubsumed(row, dirty)
            else subtractSubsumed(compactPacket(row), list.filter { it !== row })
        }
        list.clear(); list.addAll(canonical)
        cleanRows = canonical
        // Fill one complete immediate MUST branch at a time. Each promotion
        // strictly reduces a finite exclusion; admitted headers are canonical.
        if (mergeMustOverlap(list)) continue
        insert(promotion(list) ?: break)
    }
}
```

A group has at most 5 rows in the measured runs (spec §2.1). Thus a
clean test is a scan of at most 5 references. An identity hash set is
not necessary.

**(d) Extract two native parts without a change.**

- `promotion(list): FlowTree?` is the native scan of lines 69-90. It
  returns `promoted`.
- `newPart(row, before): FlowTree?` is the native delta of lines
  101-107 for one row.

**(e) Delete** the native final pass (lines 94-99) and the comment
"Prune old descendants too". Invariant F and `final_pass_noop` replace
it.

### 3.4 Properties (Lean)

The rule module `FlowGroupIncremental.lean` (spec §2.4) models a row as
(id, header, positions). The id is the object identity. The covers
`covAt` and `dom` are parameters. The implementation module
`FlowGroupIncrementalImpl.lean` imports it and adds the production
facts of §3.1.

| Claim | Theorem | Statement |
| --- | --- | --- |
| F1 | `pass_out_clean`, `pass_idem` | A pass output row is compact and not covered. The pass is idempotent |
| F2 | `final_pass_noop` | The native final pass after the loop changes nothing |
| F3 | `exit_fixpoint` | The list that the loop gives at its exit is a fixpoint |
| F4 | `passInc_eq`, `loopInc_eq` | When the clean rows are compact and pairwise not covered, the incremental pass and loop equal the native ones |
| F5 | `addAllImpl_eq` | With a total `insert` and the early return on "the same list", P3 gives the native list on every stored fixpoint |
| F6 | `delta_self` | The delta of a list against itself is empty. So the early return gives the native delta `[]` |
| F7 | `callImpl_eq` | On a stored fixpoint, one P3 call gives the native list and the native delta |
| F8 | `callNative_fixpoint`, `empty_fixpoint` | The empty list is a fixpoint, and a native call stores a fixpoint |
| F9 | `runImpl_eq` | For every sequence of values from the empty store, every P3 call gives the native list and the native delta |
| F10 | `runAbort_eq` | With calls that throw (no delta, list restored), P3 gives the native run of the calls that complete |

**Assumptions and code facts.** The proofs take these as hypotheses or
as model choices:

- A1 (code reading). The subtraction is pointwise. The cover of one
  position is a union over the leaves of the stored row
  (`LeafAlgebra.subtract`, `ap/TrieOps.kt`, spec §2.4). The model takes
  the cover as the parameter `covAt`.
- A2 (code reading). `FlowAlgebra.minusNode` is an exact difference of
  positions: a leaf minus the leaf at the same path
  (`ap/TrieOps.kt:358-365`). This gives F6.
- A3 (code fact, invariant F). Only `addAll` writes `trees`, and the
  lists start empty (§3.2). §3.3 (a) states it at the field.
- A4 (code reading). `insert`, `mergeMustOverlap` and the promotion make
  new row objects (`withRoot`, `flowTree`). They keep the object of each
  row that they do not replace. So "the same object" means "the same
  id" in the model.
- A5 (code fact). On an empty list, `mergeMustOverlap` returns false and
  the promotion scan returns null. This gives `empty_fixpoint`.
- A6 (not proved). The loop ends. The comment at `ap/Groups.kt:61-62`
  gives the reason. The model uses fuel, and F9 and F10 assume that
  each native call exits within the fuel (`AllExit`).

**Differences between model and production.**

| Model | Production | Check |
| --- | --- | --- |
| A row is a list of positions | A row is a trie with shared nodes | A1; property test (§3.5) |
| `covAt`, `dom` are parameters | `at`/`below`/`admits` of `subtractSubsumed`, and `compactPacket` | The theorems need only A1. Property test |
| `merge`, `promote`, `insert` are abstract | The native code, unchanged | The theorems need only A4 and that the loop ends after a pass |
| A throw is a call that returns no delta and keeps the list | `catch` restores `before` and rethrows | §3.3 (b); the restore has no checkpoint |
| Fuel | No fuel | A6 |

### 3.5 Tests

| Test | Content |
| --- | --- |
| `test:NativeFlowGroupReference.kt` (new, test tree only) | A copy of the native `FlowGroup` of `29c78d5c3` (lines 8-172), renamed `NativeFlowGroupReference`. It also has `isFixpoint(list)`: a full pass, the MUST merge and the promotion change nothing. It counts its own MUST merges and promotions. These counters are test code only |
| `test:FlowGroupIncrementalTest.kt` (new; from `ProtoP3FlowGroupIncrementalTest`) | (1) 3,000 random insertion sequences: one base, three fields, both layers, all FLOW tails, field and mark exclusions. After each call, the delta and the rows (with their order) equal the reference. (2) After each call, the reference `isFixpoint` holds on the P3 list (invariant F). (3) Coverage: more than 10,000 calls, more than 1,000 empty deltas and more than 1,000 non-empty deltas, as in the prototype. Also at least one reference MUST merge and one promotion. (4) If the random sequences do not reach a merge or a promotion, add one directed sequence for each (see below) |
| `test:FlowGroupIncrementalTest.kt` | "a cancelled call keeps the stored rows": store two rows, cancel the manager, call `addAll`, expect `Cancelled`, then activate and expect the same row objects |
| `test:GroupMergeTest.kt` (T1, T2, T2', T4 flow cases), `test:Run1FieldPreservationTest.kt` | Not changed. They must pass |

Directed sequences for (4), as programs for the reference and P3:

```text
MUST merge:   {x.f, x.g} ANY_TAINT/E={h} ;  x.f ANY_TAINT/E={g}   // one mark exclusion, two E, common root x.f
promotion:    x.f ANY_TAINT/E={g,h}      ;  x.f.g ANY_TAINT/E=∅   // a full child at x.f.g promotes E={h}
```

Two rows with the same root and one equal exclusion go through the
T2 branch of `insert`, not through `mergeMustOverlap`. Thus the merge
sequence uses two different roots. The test compares P3 with the
reference. It does not state expected rows by hand.

### 3.6 Cost

- **Site.** Once per `FlowGroup.addAll` call, which is once per FLOW
  value that enters a store.
- **Volume** (spec §2.1). Up to 28.3 M calls in one run (Conductor run
  6). In the tails, 58-89% of the calls change no row.
- **New work per call:**
  - an identity comparison of at most 5 row references;
  - when a row changed, one reference scan of at most 5 rows per row
    and per pass;
  - a `try` block. It costs nothing unless a throw occurs.
- **Removed work:**
  - on a call that changes no row: the whole loop, the final pass and
    the delta;
  - on every other call: the final pass, and the subtraction of a clean
    row by the other clean rows.
- **Memory.** No new field. P3 allocates less than native.
- **Prototype result** (spec §2.5). Results identical on 4 projects and
  all suites. Conductor runs 6-7: −10% and −35%. Stirling-PDF runs 8
  and 10: −20% and −13%. The share of `FlowGroup.addAll` in the
  Conductor profile windows: 5.4% → 1.5% (run 6), 10.5% → 3.6% (run 8).

## 4. P2': per-run memo of the loop-output restriction

### 4.1 Definition

`onApplied` restricts each applied value of a loop child with an exit
port `≥ 0`. The restriction of a value is `[value]` (a bypass) in run 1,
for a REACH value, and when the summary does not grow
(`LoopOutputRestriction.kt:142`). Else it observes the value and its
cuts.

```text
restrictLoopOutput(parent, loop, exit, original, value, grows):
  if bypasses(run1, grows, value): return restrict(...)                // native; no memo
  key = (parent scope, loop, exit, original, value)
  return memo[key] ?: restrict(...).also { memo.put(key, it) }         // per method runtime, per run
memo.put(key, v):
  if the memory guard cleared the memo, or it is active: keep nothing   // a miss recomputes
  if memo.size ≥ 1,000,000: memo.clear()
  memo[key] = v
```

The memo lives in the `MethodBlockRuntime` of one method in one run.
`freezeChildren` clears it at the end of the run.

### 4.2 Native code

| Site | Lines | Behavior |
| --- | --- | --- |
| `engine/MethodBlockRuntime.kt` `restriction` | 34 | One `LoopOutputRestriction` per method runtime |
| `onApplied` → `result(bounded)` | 493-546 | A loop child with an exit `≥ 0` calls `restriction.restrict` with a new `LoopRestrictionSession` (`:518-527`) for every applied value |
| `observe` | 770-876 | One `LoopConsumerObservation` per (parent scope, loop) in `observers`. It reads frozen run inputs (`config.demand`, `config.records`, `config.normalTargets`, the layout, the live locals, the end rules) and the quantum scratch `quantumQueries`. It does not read `link`. Only its debug trace reads `exit` |
| `freezeChildren` | 954-970 | Clears `observers` and the other run state at the end of the run |
| `engine/LoopOutputRestriction.kt` `restrictWithCertificate` | 135-150 | The bypass test at `:142`; else the baseline observation, budget trials and the raw fallback |
| `engine/LoopRestrictionSession.kt` | 11-42 | New per call. `certifiedFirstBudget` returns null. `trial` caches the expected descriptors of one baseline |
| `engine/RunMethodAnalyzer.kt` | 11-12, 23-28 | The only scheduled actor of a method. The run-1 static answer calls `offerStaticAnswer` outside a quantum. Run 1 always bypasses, so it never uses the memo |
| `util/SoftReferenceManager.kt`, `util/MemoryManager.kt` | 32-35; 64-75, 118 | `createRef` returns null while the memory guard is active. The guard clears all registered references before it decides OOM, and at the end of each run |

### 4.3 Code changes

Take the key of `f3910bede` (`RestrictKey`, without `gate`). Do not take
the `Proto` flags, the `SHADOW` compare, the counters, the plain
`java.lang.ref.SoftReference` or the census code of `9bf66a9b4` and
`d42a3a330`.

**(a) One bypass test** (`engine/LoopOutputRestriction.kt`).

```kotlin
/** The restriction returns [appliedValue] unchanged: run 1, a REACH value, or a summary that does not grow. */
fun bypasses(run1: Boolean, grows: Boolean, appliedValue: Facts): Boolean =
    run1 || appliedValue is Reach || !grows
```

`restrictWithCertificate` uses it at line 142. The memo uses the same
function, so the two tests cannot differ.

**(b) The memo** (new file `engine/LoopRestrictionMemo.kt`).

```kotlin
/** P2': the loop-output restrictions of one method runtime in one run.
 *
 * In one run, the restriction of an applied value reads only frozen run inputs (the demand scope views,
 * the records, the saved targets, the layout, the live locals, the end rules) and pure caches. So it is
 * a function of [Key] (spec/next-iteration-p1-p3.md §3.6; Lean `ApSpec.RestrictionMemoImpl`). A miss
 * computes the restriction, so a cleared memo is still exact. The method actor owns the memo: it is
 * not thread-safe. */
internal class LoopRestrictionMemo(
    private val refs: SoftReferenceManager,
    private val maxEntries: Int = MAX_ENTRIES,
) {
    data class Key(val parent: BlockScope, val loop: BlockId, val exit: PortId,
                   val original: PremiseKey, val value: Facts)

    private var entries: Reference<HashMap<Key, List<Facts>>>? = null

    fun getOrCompute(key: Key, compute: () -> List<Facts>): List<Facts> {
        entries?.get()?.get(key)?.let { return it }
        val values = compute()
        val map = entries?.get() ?: HashMap<Key, List<Facts>>().also { fresh ->
            entries = refs.createRef(fresh) ?: return values       // the memory guard is active: keep nothing
        }
        if (map.size >= maxEntries) map.clear()
        map[key] = values
        return values
    }

    fun clear() { entries?.clear(); entries = null }

    companion object { const val MAX_ENTRIES = 1_000_000 }
}
```

The stored list is the fresh, read-only list of
`ExactDemandResults.all()` (`store/DemandResultCoverage.kt:163`), or
the singleton of a raw fallback. `onApplied` only reads it.

**(c) The call site** (`engine/MethodBlockRuntime.kt`).

```kotlin
private val restrictions = LoopRestrictionMemo(ap.softRefs)

// onApplied, result(bounded):
val values = if (!child.isLoop || exit.ordinal < 0) listOf(bounded)
    else restrictLoopOutput(parent, child, link, exit, original, bounded, needsGate)

private fun restrictLoopOutput(parent: Entry, child: MethodBlock, link: LocalLink, exit: PortId,
                               original: PremiseKey, bounded: Facts, needsGate: Boolean): List<Facts> {
    val compute = {
        restriction.restrict(config.run1, needsGate, bounded, LoopRestrictionSession(ops, config.admissionPolicy,
            { candidate -> observe(parent, child, link, exit, original, candidate) },
            probe = { candidate, expected -> observers.getValue(parent.scope to child.id).probe(candidate, expected) },
            observeCompleted = { candidate, bundle -> observe(parent, child, link, exit, original, candidate, bundle) },
            precision = { actual -> observers[parent.scope to child.id]?.precisionCursors(actual) }))
    }
    if (restriction.bypasses(config.run1, needsGate, bounded)) return compute()
    return restrictions.getOrCompute(LoopRestrictionMemo.Key(parent.scope, child.id, exit, original, bounded), compute)
}
```

The session and its lambdas are the native ones (`:519-527`), moved
into `compute`.

**(d) End of the run.** In `freezeChildren`, add `restrictions.clear()`
to the `finally` block, next to `observers.clear()` (line 967).

### 4.4 Properties (Lean)

The rule module `RestrictionMemo.lean` (spec §3.6) proves that a sound
memo returns `f k` for every sequence of calls and clears. It needs a
function `f` on keys. The implementation module
`RestrictionMemoImpl.lean` removes that need and adds the production
facts.

| Claim | Theorem | Statement |
| --- | --- | --- |
| M1 | `call_eq`, `call_sound`, `clear_sound`, `runMemo_eq` | Rule level: a sound memo returns `f k`, whatever the clears |
| M2 | `lookup_det` | When two inputs with one key have one restriction (`KeyDetermines`), a sound memo returns the restriction of the input |
| M3 | `step_eq`, `step_sound` | One call (a bypass, a hit, or a miss that clears a full memo and stores) returns the native restriction and keeps the memo sound |
| M4 | `runImpl_eq` | For every sequence of calls, calls without a memo (`createRef` null) and clears, every call returns the native restriction |
| M5 | `key_must_determine` | A key that drops a component that the restriction reads breaks the rule. So `KeyDetermines` is a real obligation (A7) |

**Assumptions and code facts.**

- A7 (code reading, `KeyDetermines`). In one run, the restriction is a
  function of (parent scope, loop, exit, original, value):
  - The observer of (parent scope, loop) reads only frozen run inputs
    and pure caches (§4.2).
  - `link` is the only input that the key leaves out. The restriction
    does not read it. Only the trace records of `onApplied` read it.
  - `config.run1` and the gate are constant on the memo path: the memo
    serves only calls that do not bypass (gate true, runs ≥ 2).
  - The session is new per call. `certifiedFirstBudget` returns null,
    and the precision cursors are not called.

  The spec review (spec §3.6) checked this reading. The `SHADOW` launch
  of Conductor checked it on 44 M calls with 0 mismatches.
- A8 (native assumption). The cache-dependent paths give equal answers:
  the prepared C5 plan and the native C5, `skipEmptyDataReplay`, and the
  probe with cached or fresh initials. Native already assumes this.
  `test:PreparedDemandPlanTest`, `test:LoopQueryScratchTest` and
  `test:LoopAdmissionProbeTest` check it on their cases.
- A9 (code fact). One thread uses the memo. `RunMethodAnalyzer` is the
  only scheduled actor of its method, and `restrict` does not call
  `onApplied` again.
- A10 (code fact). The stored list is not changed after it is stored
  (§4.3 (b)).

**Differences between model and production.**

| Model | Production | Check |
| --- | --- | --- |
| A memo is a list of pairs | A `HashMap` with `Key.equals` | `Key` is a data class of five value-equal parts (§2) |
| `r` is a function of the input | `restrict` reads caches and the quantum scratch | A7, A8 |
| `Op.clear` | The memory guard, `freezeChildren`, the cap | M4 holds for every position of a clear |
| `Op.unavailable` | `createRef` returns null | M4 |

### 4.5 Tests

| Test | Content |
| --- | --- |
| `test:LoopRestrictionMemoTest.kt` (new) | With a counting `compute` lambda and fixture values: (1) two equal keys compute once and return the same list; (2) a change of each of the five key parts computes again; (3) `maxEntries = 2`: the third key clears the memo, so the first key computes again and the third key does not; (4) after `SoftReferenceManager.cleanup()` the next call computes; while the manager stays disabled, every call computes and nothing is kept; after `enable()` the memo keeps values again; (5) `clear()` empties the memo |
| `test:LoopOutputRestrictionTest.kt` | Add "bypasses is the bypass test of restrict": for run 1, REACH, a summary that does not grow and a growing summary, `bypasses` agrees with the `bypasses` statistic of one `restrict` call |
| Module, jvm and rule suites | Every loop fixture now runs with the memo. The prototype gate passed them with the memo on (spec §3.6) |

### 4.6 Cost

- **Site.** Once per restricted loop output that does not bypass.
- **Volume** (P2 census, Conductor): the restriction calls with a gate
  were 2.84 M of 4.84 M in run 4, 4.23 M of 24.8 M in run 6, and
  7.16 M of 10.65 M in run 8. The memo sees at most these calls.
- **New work per call:** one `Key` and one hash lookup. `Facts` and
  `PremiseKey` keep their hash in a field.
- **Removed work per hit:** one `restrict`: the baseline observation,
  the budget trials, the C2/C5 queries and the session.
- **Memory.** At most 1,000,000 entries per method runtime. An entry
  holds a `Key`, a map node, a list and the restricted values. The
  memo is soft through the analyzer manager, so the memory guard clears
  it before it decides OOM. The heap per entry is not measured (§6.2).
- **Prototype result** (spec §3.6; the prototype also kept the bypass
  calls). Results identical on Conductor, OWASP and Stirling-PDF (3
  launches). Conductor run 4: −48%. Runs 1-7: −13%. The share of
  `restrict` in the Conductor profile windows: 30.0% → 15.6% (run 6),
  33.5% → 20.0% (run 8). No fix of the Stirling-PDF stall.

## 5. Order of work

1. Commit 1: P3 code (§3.3) and P3 tests (§3.5).
2. Commit 2: P2' code (§4.3) and P2' tests (§4.5).
3. The pre-merge checks of §6.1 after each commit.
4. After both commits: the measurement of §6.2, then the updates of §7.

The two Lean implementation modules and the `ApSpec.lean` imports go in
with this proposal.

## 6. Gate

Design-guide rules 4-6 and the decisions of §1. Hold the lock
`/drive-testcomp/opentaint-go-rules/termination-next-20261119/.projects.lock`
for every suite and project launch.

### 6.1 Pre-merge checks

| Check | Pass condition |
| --- | --- |
| Module suite (2,774 native tests and the new tests) | 0 failed tests after each commit |
| Jvm suite (474 tests) | 0 failed tests after each commit |
| Rule suite, bidirectional mode | 786 success, 0 false positive, 0 false negative, 0 skipped (22 disabled, as native) |
| Lean | `lake build` succeeds, and `lake env lean audit.lean` reports 0 unexpected axioms |

### 6.2 Measurement of the whole analyzer after landing

The reference is the group A landing measurement of the same core
(`docs/reports/bidirectional-group-a-landing-20261125.md`). One launch per
project, three for Stirling-PDF. Keep the profile windows of the landing
campaign. Run OWASP when no other user loads the host (mean load near
3).

| Check | Expected (prototype evidence, spec §2.5 and §3.6) |
| --- | --- |
| Results | Confirmed and provisional results and SARIF code flows identical to the parent: OWASP 2,633; Conductor at its run-8 TIMEOUT byte-identical; Stirling-PDF identical to the parent launch with the same end (34 when OK, 32 at a TIMEOUT); ThingsBoard OOM in run 1 with no results, as the parent |
| Time | Conductor runs 1-7 faster than 652.5 s (P3 alone 576.0 s, P2' alone 568.1 s; the pair is not measured). Stirling-PDF runs 8 and 10 not slower than the parent. OWASP engine time not worse than 121.0 s beyond the run-1 noise |
| Memory | Peak RSS inside the parent range (9.49-10.26 GiB). Largest heap after GC not higher |
| Memo heap | `jcmd <pid> GC.class_histogram -all` in Conductor run 8: the instance count and bytes of `LoopRestrictionMemo$Key` and of the `HashMap` nodes. The option `-all` does not force a GC, so the soft memo stays |
| Profiles | The share of `FlowGroup.addAll` and of `LoopOutputRestriction.restrict` in the Conductor windows of runs 6 and 8 (the diagnosing quantities) |

### 6.3 Withdrawal

Revert a commit when one of these occurs:

- a pre-merge check fails;
- a confirmed or provisional result differs from the parent;
- the time or the memory of a project is worse beyond the spread of the
  parent launches;
- for P2': the quiet OWASP launch shows a regression in runs 2-11 that
  is larger than the noise of run 1 (spec §3.6).

## 7. Spec and model updates after the measurement

- `next-iteration-p1-p3.md` header and §0: P3 and P2' landed, with the
  commit ids and the measurement.
- `docs/design/bidirectional-next-iteration-20261125.md`: the status
  line.
- `ap-impl.md` §4.3: its `FlowGroup` sketch predates `addAll`. Add
  invariant F and the landed `addAll`.
- `demand-trie-loop-restriction.md` (`restrictScalar`): add one line. A
  method runtime computes the restriction of one key once per run, while
  the memo is not cleared.

## 8. Calls made in this proposal

These are implementation choices. None changes a result, by §3.4 and
§4.4. The owner can change each of them.

| # | Call | Reason | Alternative |
| --- | --- | --- | --- |
| C1 | P2' bound: at most 1,000,000 entries per method runtime; clear all when full | It is the measured prototype bound (Conductor run 4 −48%) | A larger bound or a two-generation memo can keep more hits in Conductor run 8 (2.8 M distinct keys, 4 full clears in the prototype). It is not measured |
| C2 | The P2' memo is soft through the analyzer manager (`ap.softRefs`), not a plain `SoftReference` | The memory guard clears it before it decides OOM, and at the end of each run. In the prototype launches the guard fired only in Conductor runs 2-3, so the measured hits do not change | A plain `SoftReference`, as in the prototype. The JVM clears it only near an `OutOfMemoryError`, after the guard |
| C3 | The P2' memo serves only the calls that do not bypass. The key has no gate and no run flag | A bypass costs as little as a lookup. In Conductor run 6, 83% of the restriction calls bypass, and the prototype kept an entry for each of them | Keep all calls, as in the prototype. It fills the cap sooner |
| C4 | The P2' key keeps `exit` | It is the measured key. Today the observer does not read `exit`, so a key without it would give more hits | Drop `exit` after a new code reading and a measurement |
| C5 | P3 restores the list on a throw | Invariant F then holds for every reader after a cancellation. The restored state is a native state (§2) | No restore; the spec showed that the cancelled run ends today (spec §2.8) |
| C6 | P3 returns early on "the same row objects", not on "`insert` returned null" | `insert` returns a value only when it changes the list, and it can return null after it removed a row. The object test covers both cases | The prototype test `inserted == null && sameRows(...)`. It is equal, with one more condition |

## 9. Checklist and blind spots

```text
[x] Failure class and real trace: spec §2.1 (P3), §3.5 (P2')
[x] Ablation on the real case: exact rules; the SHADOW modes replace an ablation (spec §2.4, §3.6)
[x] Native prototype: P3 (4 projects, Stirling-PDF x3); P2' (Conductor SHADOW and ON, OWASP x2, Stirling-PDF x3)
[x] Execution site and volume: §3.6, §4.6
[x] Selected semantic scope: §2 (no observable change; the throw behavior of P3; the P2' diagnostics)
[x] Proof scope and model differences: §3.4, §4.4 (27 theorems; propext and Quot.sound only)
[x] Withdrawal condition: §6.3
```

- **Landed forms differ from the measured prototypes in three
  details.** P2' serves only calls that do not bypass (C3) and uses the
  analyzer manager (C2). P3 restores its list on a throw (C5). The
  proofs cover all three. No launch measured them.
- **The pair P3 + P2' is not measured.** Both act on the same Conductor
  runs. §6.2 measures the pair.
- **OWASP time for P2' is not settled.** The one quiet launch was 9.2 s
  slower, 6.5 s of it in run 1, where P2' does not act (spec §3.6).
- **A7 is a code reading.** The `SHADOW` check covers Conductor only.
  OWASP and Stirling-PDF ran with the memo on and gave identical results,
  but they did not compare each hit.
- **A8 is a native assumption.** If the cached and the uncached paths
  ever differ, the memo keeps the first answer for the run.
- **The memo heap per entry is not measured.** §6.2 adds a class
  histogram.
- **The throw path of P3 has a test only for a cancellation before the
  first write.** A cancellation in the middle of a call has no
  deterministic test. The restore is two lines without a checkpoint,
  and `runAbort_eq` models it.
- **Property test scope.** One base, three fields, depth 3 or less.
  §3.5 (3) and (4) add a coverage check for the MUST merge and the
  promotion. It is not known yet how often the random sequences reach
  them.
- **Termination of the `addAll` loop is not proved** (A6). P3 does not
  change the loop steps.
- **No effect on the stall.** P3 and P2' do not fix the Stirling-PDF
  stall or the Conductor run-8 timeout. P2'' is the next step
  (spec §5).

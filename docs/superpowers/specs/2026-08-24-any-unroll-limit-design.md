# Carrying the `[any]` unroll budget on the fact

Bounding the `[any]` explosion with a budget that travels with the value instead of sitting in a
per-context counter.

- **Branch**: design targets `saloed/14-any-premise-impl` @ `50ccd990f`.
- **Scope**: the tree access-path backend (`ApMode.Tree`, the default). Cactus and automata are out
  of scope; §12.4 says what they need.
- **Supersedes**: the per-`(MethodEntryPoint, AccessPathBase)` counter
  (`TreeInitialFactAbstraction.unrolledFactCount`, TIFA:401), currently hard-wired to `100` at
  TIFA:517 with its `-D` read commented out.

Path abbreviations: **TIFA** = `access/tree/TreeInitialFactAbstraction.kt`, **AT** =
`access/tree/AccessTree.kt`, **AP** = `access/tree/AccessPath.kt`, **SUB** =
`access/tree/MethodTreeAccessPathSubscription.kt`, all under
`core/opentaint-dataflow-core/opentaint-dataflow/src/main/kotlin/org/opentaint/dataflow/ap/ifds/`.

---

## 1. Why the current budget fails

The existing budget is keyed by **context**, not by value:

```kotlin
// TIFA:401-408
private var unrolledFactCount = 0

val anyUnrollAllowed: Boolean
    get() = anyUnrollLimit < 0 || unrolledFactCount < anyUnrollLimit

fun accountUnrolledFact() { unrolledFactCount++ }
```

One counter per `(method entry point, base)`, incremented at TIFA:164, checked at TIFA:140. Three
measured consequences, all on the conductor witness (`WorkflowResource#rerun` → … → `decide`):

**(a) It is bypassable.** `accountUnrolledFact()` is reachable only from `unrollAnyAccessors`
(TIFA:125). The other channel that grows facts — the spine rebuild in `AccessNode.filterStartsWith`
(AT:1707) — never touches it. Instrumented: at no cap, **16,249 accounted unrolls and 0 unaccounted**;
at cap 0, **0 accounted and 482,233 unaccounted**. The two paths are *alternatives*. Capping the
counter does not remove work, it **diverts** it.

**(b) Charging the second channel against the same counter is a no-op.** Prototype
`saloed/30-charge-hidden-unroll` did exactly that. Conductor, four arms (off / 100 / 10 / 0):
`rc=254` in all four, 901–929 s, 14,192–15,196 premises, **2 findings in all four**. The refusals fire
(1,052–1,345); the counter they consult is dominated by the unroller, so they fire in the wrong
places.

**(c) The counter cannot see what it protects.** It counts facts unrolled *for a base in a method*.
What actually diverges is a single derivation chain growing one link per round:

```
arg0.p.[any].*  --filterStartsWith(arg0.p.f.*)-->  arg0.p.f.[any].*  --…-->  arg0.p.f.g.[any].*  …
```

`getChild`'s `isCoveredByAny` arm (AT:537-541) is a **fixed point**: it consumes nothing and returns
the `[any]` node re-prepended, so the descent always succeeds, and the rebuild at AT:1750 puts one
more concrete link above the `[any]`. **53,735 / 53,735** reads through that arm returned the node
unchanged. `[any]` is inexhaustible, not wide: it matched 116 distinct accessors against `.*`'s 1,080,
and `.*` converges because its reads **consume** — the accessor joins a monotonically growing
exclusion set.

The decisive control: a source tainting the same object graph through concrete fields with **no
`[any]` anywhere** converges `rc=0` in 43.8 s with 9,135 premises and byte-identical SARIF
(`2e6dd9bc2445a9a5`), against `rc=253` and 64,467 premises with `[any]`. Chains reached 13 links and
were 72.1 % prefix-closed, so depth alone is not the problem.

**The problem is a growth step with no progress measure.** This design gives it one, and attaches it
to the fact it grows.

---

## 2. The invariant

> **I0.** Every fact tree carries a remaining `[any]`-unroll budget — a small non-negative integer
> `limit` — on its **root `AccessTree.AccessNode`**, not on the `AccessTree` wrapper. Every operation
> that produces a tree produces its root node's `limit` explicitly. No operation may raise a `limit`
> above its inputs'.

The field is **immutable**, like every other field of `AccessNode`: the tree is copy-on-write, so a
node with a different limit is a different node, produced by the ordinary construction path. Nothing
in this design mutates a published node.

`limit = 0` does **not** mean "drop the fact". It means "this fact may no longer trade an `[any]` for
a concrete accessor" — it must stay coarse. Coarse is the **sound** direction (§9.2), which is what
makes exhaustion safe and distinguishes this from every cap tried so far.

Derived:

- **I1 (monotone descent).** Along any single derivation chain, `limit` never increases.
- **I2 (bounded mint).** `limit` is minted only where a fact enters the analysis with no predecessor
  to inherit from (§4.1 enumerates all four such places), always at the configured maximum `L`. Every
  other site copies, mins, or decrements.

I1 + I2 are the termination argument (§9.1).

---

## 3. Representation — the hard part

Where the limit physically lives is more constrained than anything else in this design, and the
constraints point somewhere other than the obvious place.

### 3.1 The wrapper is erased at every storage boundary

```kotlin
// access/tree/TreeFinalApAccess.kt:4-9
override fun getFinalAccess(factAp: FinalFactAp): AccessTree.AccessNode = (factAp as AccessTree).access
override fun createFinal(base: AccessPathBase, ap: AccessTree.AccessNode, ex: ExclusionSet): FinalFactAp =
    AccessTree(apManager, base, ap, ex)
```

**No storage in the package ever stores an `AccessTree`.** Every one stores the bare root
`AccessNode`; the wrapper is rebuilt on read-out, usually with an invented exclusion set
(`ExclusionSet.Universe` at `common/CommonZ2FSet.kt:62`, `CommonNDF2FSet.kt:224,263`,
`CommonZ2FSummary.kt:267`, `CommonNDF2FSummary.kt:392`).

**A limit on `AccessTree` would be destroyed at every boundary.** It has to be on `AccessNode`. This
is why the invariant says "the tree *root node* carries the limit".

### 3.2 The field

```kotlin
// AccessNode, a normal immutable constructor field -- NO default value, so the
// compiler catches every construction site that forgets it.
@JvmField val anyLimit: Byte
```

**It is free.** `AccessNode` has no superclass; its fields are 5 references, 2 `Long`, 1 `Int`, 1
`Byte` (`interned` / `isAbstract` / `isFinal` are constructor *parameters*, consumed by the init block
at AT:387-395, not fields). Under compressed oops — every JVM arg in the repo is `-Xmx8g`, far below
the 32 GB threshold:

```
header 12 | maxDepth 4 → 16 | hash 8 → 24 | size 8 → 32 | flags 1 → 33 | pad 3 → 36 | 5 refs × 4 → 56
```

**53 bytes of content, 56 after alignment, with three spare bytes at offsets 33–35.** One more `Byte`
lands in existing padding: 56 → 56. Confirm with JOL (§12.1), but the conclusion is robust — anything
up to three extra bytes is free.

A separate field is preferable to packing into `flags` bits 5–7 (which are genuinely unused, AT:2032-2036).
The bits would cap `L ≤ 7` and buy nothing, since the byte is already free.

### 3.3 Where the limit sits relative to identity — and the trap that decides it

The tempting move is to fold the limit into `hash` and `equals` so the interner keeps the variants
apart. **That breaks the analysis silently:**

```kotlin
// AT:488-489
val isLegalNodeBelowTaintMark: Boolean
    get() = this == manager.finalNode || this == manager.abstractNode || this == manager.abstractFinalNode
```

That is structural `==`, not `===`, and it gates prepending a taint mark at AT:565. If `anyLimit`
joined `equals`, a leaf at limit 3 would stop being `== manager.finalNode`, `addParentIfPossible`
would refuse a legal taint-mark prepend, and **findings would be lost with no error**.

So:

> **`anyLimit` stays out of `hash` and out of `AccessNode.equals` / `hashCode`. It goes into
> `AccessTreeInterner.InternStrategy.equals` only. `intern` keeps `putIfAbsent` unchanged.**

`InternStrategy` being *stricter* than `equals` is legal — fastutil requires equal keys to have equal
hash codes, not the converse.

The deeper reason this is right: **the interner must have no semantic authority.** It is opportunistic
(`TreeSetWithCompression.kt:14-17` interns directly only at `size ≥ 100_000`; the batch path needs 100
elapsed operations *and* `maxNodeSize ≥ 100`), soft-referenced and rebuilt **empty** when the reference
clears (`AccessTreeSoftInterner.kt:67-79`), per-storage rather than global, and there are two
*throwaway* interners at AT:1380 and AT:1604. Any design that puts the `min` in `intern` makes
correctness depend on GC timing and on rate-limit thresholds. Keeping the limit out of `hash`/`equals`
but in `InternStrategy` means interning never *changes* a node's limit — it only declines to share
between variants.

This also avoids touching `hash` at all. Worth recording why that matters: only **bit 2** is provably
free there (both shifted terms are `≡ 0 mod 8`, and the `isAbstract`/`isFinal` term is `≤ 3`), so a
3-bit limit would force a re-layout that pushes the child term from `shl 5` to `shl 8` — costing four
levels of depth capacity before a child's hash bits shift out of the 64-bit word, on facts that
already reach 13 concrete links.

### 3.4 The `⊤` canonicalisation — one line, and it does most of the work

> A node with no `[any]` anywhere in reach can never spend the budget, so its limit is meaningless.
> **Canonicalise it to `⊤`.**

`AccessNode`'s init block already computes exactly this predicate, bottom-up, *before* `flags` is
assigned (AT:372-378 → AT:387-395). One more line in the same block:

```kotlin
this.anyLimit = if (containsAnyDeep) requestedLimit else TOP
```

Immutability-compatible — computed once, in the init block, exactly like `flags`.

What it buys:

- **The four singletons stay unique.** A structureless leaf provably lands on `⊤`: `accessors == null`
  ⟹ `accessorIndex` returns −1 (AT:490-493) ⟹ `containsAnyAccessor()` is false, and
  `accessorNodes == null` skips AT:368-378. So `createElementAndField`'s singleton fast path
  (AT:2249-2250) stays valid, and the ~10 sites that select a singleton need no per-limit variant.
- **Fragmentation is confined to the `[any]` spine.** Every subtree beside it, and every leaf, is `⊤`
  and shares exactly as it does today.

**One obligation it creates:** a prepend that *introduces* an `[any]` over a `⊤` node
(`prependAnyAccessor` → `create(ANY_ACCESSOR_IDX, …)` at AT:807) would refill to `⊤`. It must take its
limit from the operation's context, not from the inner node. This is a termination obligation, not a
soundness one — refilling to `L` is no worse than a fresh mint — but it is the one place P2's
"inherit from the inner node" does not apply.

### 3.5 How much fragmentation is left

Less than the naive estimate, for a structural reason worth stating: **on the dominant channel the
limit is already a function of the shape.** A decrement is spent exactly when a concrete link is
prepended above the `[any]` (§6), so a tree with `k` such links was reached with `k` decrements and
has limit `L − k` — which is precisely §10.1's `anyPrefixDepth`. Where the carried limit and the
structural measure coincide, **a shape can only ever exist at one limit and fragmentation is exactly
zero.**

Variants arise only where a *foreign* budget is imported onto a shape that did not itself spend it:
the `min` at concat (AT:1433/1641), at merge (AT:1145, AT:1178), and at storage collision. Since
limits only fall, the variant sequence for a shape is a chain `L → … → k`, never a cycle:
**at most `L + 1` variants per shape, ever.** Expected: 1–2.

Two things make it worse and are worth knowing before measuring:

- **Interners are per-storage, not global** (`TreeSetWithCompression.kt:10`,
  `MergingTreeSummaryStorage.kt:13`, `SUB:26`, `TreeFinalFactList.kt:24`, `TIFA:36`), so a shape
  already exists once per storage today; limits multiply within each.
- **`mergeNodeLoop`'s memo is identity-keyed** (`AccessNodeMergePair`, AT:1122-1132). Two limit
  variants of one shape are different identities, so the memo misses and merge work is redone per
  variant. Fragmentation costs CPU here, not only heap.

One consequence of keeping the limit out of `AccessNode.equals`: two facts differing only in limit are
`==`, so a value-keyed collection can dedup them and keep whichever arrived first. Under min that is
the same "weaker bound, never unsound" trade as §7.3, and the same counter measures it.

### 3.6 Identity plumbing

| what | change |
|---|---|
| `hash` (AT:351-396) | **none** |
| `AccessNode.equals` / `hashCode` (AT:406-422) | **none** |
| `InternStrategy.equals` (`AccessTreeInterner.kt:15-29`) | compare `anyLimit` |
| `markInterned` (AT:1494-1502) | must **copy** it. This is the classic drop site — `anySuffixMatcher` is deliberately *not* copied there (AT:330-338), so there is no preservation precedent. Giving the constructor parameter **no default value** is what turns this from a silent bug into a compile error |

Construction sites: the private constructor's five callers (AT:1494, 2018, 2180, 2210, 2254) and the
`create` overloads at AT:2169, 2176, 2189, 2195, 2221, 2243, 2267, 2276. The bulk of the plumbing is
the general builder at **AT:2221, with 14 call sites** (AT:733, 953, 973, 1040, 1044, 1119, 1170,
1220, 1228, 1699, 1850, 1931, 1991, and `AccessTreeAnySuffixMatcher.kt:162`).

### 3.7 Serialization — free, and stale-cache-safe

The node's wire mask uses one byte and only three of its bits:

```kotlin
// AT:1946-1956
var mask = 0
if (node.isFinal) { mask += 1 }
if (node.isAbstract) { mask += 2 }
if (node.deepAccessorExclusion != null) { mask += 4 }
write(mask)
```

**Bits 3–7 are free at zero byte cost.** Put a 3-bit limit in bits 3–5, **biased by one** so `0` means
"absent / `⊤`":

```kotlin
if (node.anyLimit != TOP) mask += (node.anyLimit + 1) shl 3
// read: ((mask shr 3) and 0x7).let { if (it == 0) TOP else (it - 1).toByte() }
```

The bias is what makes it safe, and it matters more than it looks: **there is no version tag anywhere
on this path** — not on the node mask, not in `TreeSerializer.kt:21-48`, not in `ApSerializer`, not in
`EdgeSerializer`, not in `MethodSumariesSerializer.kt:23-34`, and not on the persisted entity in
`JIRSummariesFeature.kt:272-315` (whose `apModeId` discriminates the *backend*, not the format).
`loadSummaries` reads stale gzipped blobs from previous runs back with no validation at all.

With the bias, an old blob decodes to `⊤` (matching §4.1 M4: sound, permissive), and an old binary
reading a new blob simply ignores bits 3–5 because it masks with 1/2/4 (AT:1978-1981). Backward *and*
forward compatible, no version tag needed.

Any encoding that adds **bytes** — a separate `write(limit)`, a widened mask — would shift the stream
under every subsequent `readInt()`/`readLong()` and misparse every stale cache catastrophically. If
that is ever needed, add a version first: either a magic + version ahead of
`MethodSumariesSerializer.kt:26`, or a `formatVersion` property beside `apModeId`
(`JIRSummariesFeature.kt:300`) with the query filters at `:278`/`:300` extended to match — the latter
also gives free invalidation instead of misparse.

Reader paths: AT:1990-1992 (structureless-leaf early return) is automatically consistent under §3.4,
since a leaf is always `⊤`. AT:2018 (the private constructor) must pass the limit explicitly.

---

## 4. Propagation rules

`L` = the mint value. `⊤` = "nothing recorded", read as `L`.

| # | operation | rule | sites |
|---|---|---|---|
| P1 | **mint** — a fact entering the analysis | `limit := L` | see §4.1 |
| P2 | **prepend** — `create(accessor, node)` AT:2194, `addParentIfPossible` AT:546, `addParent` AT:728, `addParentFieldAccess` AT:936 | `limit(result) := limit(inner)` | prepending inherits. **Exception**: a prepend that *introduces* an `[any]` (`prependAnyAccessor` AT:787) must take its limit from context, not from a `⊤` inner node — §3.4 |
| P3 | **read** — `getChild` AT:526, `readAccessor` AT:77 | `limit(child) := min(limit(parent), limit(childNode))` | a read alone never decrements — it is the read **paired with a prepend of the same accessor** that does (P8, §6) |
| P4 | **delta** — `mergeAddDeltaStep` AT:1178, `NodeAccessTreeDelta` AT:150, `EmptyAccessTreeDelta` AT:139 | `limit(delta) := limit(fact root)` | a merge delta's root sits at the same base as both operands (AT:1220-1223) |
| P5 | **concat** — `concatToLeafAbstractNodes` AT:1433/1641, `AccessTree.concat` AT:212 | `limit(result) := min(limit(this), limit(other))` | folds a grafted subtree's budget into the root at graft time |
| P6 | **merge** — `mergeAdd` AT:1134, `mergeAddStep` AT:1145, `mergeAddMaybeNull` AT:518, `bulkMergeAddAccessors` AT:1092 | `limit(result) := min(limit(a), limit(b))` | same lattice direction as the existing `intersectDeepExclusion` (AT:1139) |
| P7 | **structure-preserving** — `rebase`, `exclude`, `replaceExclusions`, `filterFact`/`filterAccessNode`, `abstractOnly`, `removeAbstraction`, `clearChild`, `clearAllAccessorOccurrences`, `annotateAbstractNodes`, `internNodes`, `markInterned` | `limit` unchanged (**must be copied explicitly** — `markInterned` AT:1494 rebuilds through the private ctor and is the classic drop site) | |
| P8 | **spend** — TIFA unroll (§5), the covered read + prepend in `filterStartsWith` (§6) | `limit(result) := limit(input) − 1`; refuse at `0` | the only decrements |
| P9 | **storage collision** — the eleven merge sites | `limit(node) := min(limit(node), limit(incoming))`; see §7.2-7.3 | a slot holds one merged tree, so it carries one budget. **Interning is not on this list** — it has no semantic authority (§3.3) |

**Min at every meet, without exception.** P3, P5, P6 and P9 are all the same rule: whenever two
budgets would have to coexist in one object, they cannot, and the lower one wins. There is no place
in this design where a limit goes up.

That uniformity is what makes the bound hold. The tempting alternative — treat a shape arriving twice
as *alternative derivations* and take the max, which would be the usual IFDS join and would make the
assignment a least fixed point — fails here for a concrete representation reason: there is no fact
*set* to join over. A storage slot holds a single tree formed by `mergeAdd`, and taking the max would
let a low-budget component ride a high-budget one's budget. §7.2 gives the argument in full.

`sum` / `subtract` are not options: neither is idempotent, so neither converges against the merges'
"nothing changed" guards (AT:1158-1165, AT:1212-1218).

### 4.1 Mint sites

The limit is minted wherever a fact enters with no predecessor to inherit from. There are four, and
the first is the one that matters:

**M1 — source-rule fact birth.** `taint/Source.kt:16-29` (`TaintSourceActionEvaluator.evaluate`) →
`taint/AccessPathCreationUtils.kt:12-21` (`mkAccessPath`) → `TreeApManager.createFinalAp` (`:112-113`).
This is the *only* mint that carries information: the `[any]` enters the fact right here, when the
rule's position is `AnyAccessorAfter`:

```kotlin
// jvm/ap/ifds/taint/TaintEvaluator.kt:67-70   (Go twin: go/analysis/GoSequentTaintUtil.kt:63-66)
fun ActionPosition.resolveAp(): PositionAccess = when (this) {
    is ActionPosition.Exact -> position.resolveAp()
    is ActionPosition.AnyAccessorAfter -> PositionAccess.Complex(position.resolveAp(), AnyAccessor)
}
```

Because this is the one point that knows *which rule asked for the `[any]`*, it is also where a
**per-rule `L`** could later be attached without any further plumbing. Not in scope for v1 — `L` is
global — but the design should not foreclose it, and §15 explains why it may end up being the better
lever than `L` itself.

**M2 — base-only fact birth**, where there is no predecessor at all:
`MethodAnalyzer.kt:1424-1425` (`EmptyMethodAnalyzer.addSummary`) and `MethodAnalyzerEdges.kt:172-173`
(the static-state pair). Mint `L`.

**M3 — the manager singletons** `mostAbstractFinalAp` / `createFinalAp` (`TreeApManager.kt:109-113`)
— these contain no `[any]`, so they are `⊤` by the §3.4 canonicalisation.

**M4 — deserialisation.** `TreeSerializer.readFinalAp` (`TreeSerializer.kt:50-61`) and
`Serializer.readAccessNode` (AT:1976). A deserialised summary has no in-process predecessor; minting
`L` is sound but permissive. See §14 R7.

Everything else inherits. Note in particular **M-not: `TreeInitialFactAbstraction:101` is not a
mint** — it synthesises a fresh `AccessTree` from a chain with no parent fact in scope, but its
budget must come from the fact whose frontier produced the chain (§5.3b), not from `L`. Treating it
as a mint would hand every re-abstracted fact a full budget and destroy the bound.

### 4.2 The complete checklist

Every point where the limit needs explicit handling rather than falling out of P2–P7. Four of them
have no single obvious parent, and those are where the design can go wrong quietly.

| # | site | file:line | action | obvious parent? |
|---|---|---|---|---|
| 1 | source-rule fact birth | `taint/Source.kt:26` → `AccessPathCreationUtils.kt:19` | mint `L` (M1) | n/a |
| 2 | base-only fact birth | `MethodAnalyzer.kt:1424-1425`, `MethodAnalyzerEdges.kt:172-173` | mint `L` (M2) | n/a |
| 3 | caller → callee rebase | `TaintAnalysisUnitRunner.kt:384/395/406`, `SummaryEdgeSubscription.kt:86/121/165` | carry (P7) | yes |
| 4 | callee-entry re-abstraction | `TIFA:101`, via `MethodAnalyzer.kt:267` / `:620` | **re-seed from the frontier fact** | **no** — §5.3b |
| 5 | summary instantiation | `MethodCallSummaryHandler.kt:115-116` (`concat`) | **min of the two parents** (P5) | **no** — see below |
| 6 | the read + prepend pair | `filterStartsWith` AT:1734 + AT:1750 | **decrement, then absorb** (P8, §6.3) | yes |
| 6b | the second such pair | `taint/Cleaner.kt:209-218` | same primitive, deferred (§6.0, step 6) | yes |
| 9 | prepend that *introduces* an `[any]` | `prependAnyAccessor` AT:787, AT:807 | **take from context** — a `⊤` inner node would refill the budget | **no** — §3.4 |
| 7 | abstraction collapse | `JIRMethodSequentFlowFunction.kt:594` (`abstractOnly()`), Go `GoMethodSequentFlowFunction.kt:240/331` | carry unchanged (P7) | yes — see below |
| 8 | storage round-trip | `CommonZ2FSet.kt:35/62`, `CommonF2FSet.kt:45/89/111` via `TreeFinalApAccess.createFinal` | **join on `mergeAdd`** (P9, §7.2) | **no** |

**On #5.** `mappedSummaryFact.concat(typeChecker, summaryEffect.delta)` grafts a delta derived from
the *caller's* fact onto a fact derived from the *callee's* summary exit. Neither is "the" parent, and
`min` is the choice. The justification is not symmetry but termination: the result is a fact in the
caller that may grow further, so it must be no more permissive than either thing it was built from.
Taking `max` here would let a fresh callee summary refill a caller fact's budget on every application
— the "fresh budget per fact" failure mode — and the chain bound of §9.1 would not hold.

**On #7.** `abstractOnly()` (AT:95-96) discards the concrete subtree and keeps only `.*`. It is
tempting to treat it as a reset, but `.*` reads **consume** — that is exactly why the no-`[any]`
control converges — so the resulting fact cannot exploit a budget it does not spend. Carry the limit
unchanged and let it be irrelevant. Go inlines this branch twice
(`GoMethodSequentFlowFunction.kt:239-247`, `:330-338`) with no `abstractOnly()` and no alias fan-out,
so the two languages differ here; the rule is the same for both.

---

## 5. Spend site 1 — TIFA

### 5.1 The change

The check at TIFA:140 moves from the base's counter to the fact's limit:

```kotlin
// TIFA:140, today
if (!anyUnrollAllowed) return@forEachInt
```

- **budget remains** → unroll as today; the facts built at TIFA:161 carry `limit − 1` (P8).
- **budget exhausted** → do not unroll; emit the **`[any]` premise and `[any]` final** pair instead.

### 5.2 The fallback already exists

The coarse pair is not new work. TIFA:262-267 already emits it, and TIFA:94-105 is its single
construction point — both halves folded from the same `ReversedApNode` chain, so they are guaranteed
to name the same accessor sequence:

```kotlin
// TIFA:97-104
val initialAbstractAccessNode = apManager.createNodeFromReversedAp(abstractAccess)
val initialAbstractAp = AccessPath(apManager, concreteFactBase, initialAbstractAccessNode, Empty)
val apAccess = apManager.createAbstractNodeFromReversedAp(abstractAccess)
val ap = AccessTree(apManager, concreteFactBase, apAccess, Empty)
facts.addAnalyzedInitialFact(initialAbstractAccessNode, exclusions = IntOpenHashSet())
abstractFacts.add(initialAbstractAp to ap)
```

Seven tests in `AnyPremiseAbstractionTest.kt` already pin its behaviour (`:96, :107, :123, :140,
:341, :355, :372`). **The work is re-keying *when* it fires, not changing *what* it emits.**

Note the two constructor families and pick deliberately: the raw fold above does **not** collapse
`[any]`, while the `prependAccessor` family (AP:71 → `addParent` AP:550 → `prependAnyAccessor`
AP:629) does. TIFA relies on the raw family because the walk it folds already respects the
"no `[any]` reachable from another `[any]` through a covered-only path" invariant.

### 5.3 Two structural obstacles that must be handled

**(a) The demand memo commits as it reads.**

```kotlin
// TIFA:462-469
fun unrollAccessors(accessors: IntOpenHashSet): IntOpenHashSet {
    val current = unrolled ?: IntOpenHashSet().also { unrolled = it }
    val result = IntOpenHashSet()
    accessors.forEachInt { if (current.add(it)) result.add(it) }   // :466 -- mutates on read
    return result
}
```

A collected-but-unhonoured request burns the memo **permanently**. This is why TIFA latches
`enumerateAnyFrontier` once per round at TIFA:92 and refuses to even *collect* when the base is cut.

With a per-fact budget, one frontier can be out of budget while another at the same base is not, so
**the latch must be recomputed per frontier, not per round**, or the memo burns for frontiers whose
fact is out of budget. Concretely: TIFA:221's `if (enumerateAnyFrontier)` becomes a test on the
budget of the fact at `state.added`, evaluated at that point.

**(b) The refusal is invisible to the caller.**

`unrollAnyAccessors` returns `AccessTreeNode?` (TIFA:128) and `null` conflates *five* outcomes —
budget (`:140`), strategy (`:143`), accessor type filter (`:153`), node type filter (`:159`), illegal
shape (`:161`). The caller discovers a budget refusal only by re-polling `facts.anyUnrollAllowed` at
TIFA:111. **That poll stops answering the question once the budget is per fact**, so
`unrollAnyAccessors` must return an explicit refusal signal (e.g. `Pair<AccessTreeNode?, Boolean>` or
a small result type) and TIFA:111-119's re-walk must be driven by it.

### 5.4 A latent trap on the coverage predicate

`AnyAccessorUnrollStrategy.AnyAccessorDisabled.unrollAccessor` **throws** rather than returning false
(`access/ApManager.kt:56-58`), and it is installed for the whole prescan phase
(`TaintAnalyzer.kt:133-135`). `TreeApManager.isCoveredByAny` (`:50-51`) and `AccessNode.contains`
(AT:513-515) call it unguarded. Any new coverage query added by this design — §6.2's predicate in
particular — **must** use the guarded idiom (`Accessors.kt:166-170`, `tryAnyAccessorOrNull`) or it
will stall the prescan. This exact bug was hit and fixed once already on an earlier prototype
(openmrs stalled at `Progress: 1/7367` with 0 findings).

---

## 6. Spend site 2 — the read + prepend pair

### 6.0 Which sites have the pattern, and why almost none do

A covered read on its own is harmless. `getChild`'s `isCoveredByAny` arm (AT:537-541) consumes
nothing and hands back the `[any]` node, but *what the caller does next* decides whether anything
grew. The damaging pattern is narrower than "a covered read":

> **read accessor `a` through an `[any]`, then prepend `a` back on top of the result.**

That pair materialises `a` above the `[any]` — a concrete link the fact did not have — which is
precisely an `[any]` unroll. And it is only *recognisable*, and therefore only *absorbable*, where
both halves are visible in one place.

`filterStartsWith` is such a place. It accumulates the accessors it read into `parentAccessors` and
folds them straight back on:

```kotlin
filteredTreeNode.getChild(accessor)?.also { parentAccessors.add(accessor) } ?: return null   // AT:1734-1736
...
return parentAccessors.foldRight(filteredTreeNode, ::create)                                 // AT:1750
```

**Almost nowhere else pairs them** — one other site does, and is treated below. The reads that look
superficially similar do something structurally different — they *rebase* rather than re-prepend, so the concrete prefix is replaced, not extended:

```kotlin
// jvm/.../MethodFlowFunctionUtils.kt:89-93
fun FinalFactAp.readAccessorTo(newBase: AccessPathBase, accessor: Accessor): FinalFactAp =
    readAccessor(accessor)?.rebase(newBase) ?: error("Can't drop field")

fun FinalFactAp.writeToAccessor(newBase: AccessPathBase, accessor: Accessor): FinalFactAp =
    prependAccessor(accessor).rebase(newBase)
```

So the field read at `JIRMethodSequentFlowFunction.kt:442` turns `x.[any].*` read at `f` into
`y.[any].*` — the destination local, at the same depth. No growth. The write at `:543` does prepend,
but the accessor comes from the *statement*, not from a preceding covered read of the same accessor,
so there is no pair to absorb. Go behaves the same way (`GoMethodSequentFlowFunction.kt:250`).

| site | shape of the operation | charges? |
|---|---|---|
| `AccessNode.filterStartsWith` AT:1734 + AT:1750 | **read + prepend, same accessors** | **yes** |
| `TIFA.unrollAnyAccessors` :159-162 + `addReversedApParents` :184-187 | **read + prepend** — the acknowledged unroll | **yes**, via §5 |
| `AccessTree.readAccessor` AT:78 → `readAccessorTo` | read + **rebase** | no |
| `writeToAccessor` | **prepend** with no paired read | no |
| `equalTo` AT:593, `containsStrict` AT:613, `containsThroughAny` AT:649, `matchThroughAny` AP:246, `splitDeltaStrict` AP:334/368 | boolean queries | no |
| `TIFA:228` | `[any]` taken **zero** times | no |
| **`Cleaner.cleanConcrete`** `taint/Cleaner.kt:209-218` | **read + prepend, same accessor** | **yes** — see below |
| `Cleaner.kt:181-185` | read + prepend of `[any]` onto `[any]` content | no — no concrete link is materialised |
| `AliasUtil.kt:44-51, 94-97` | read, then rebase + prepend of a *different* (alias) path; `AnyAccessor` maps to `null` in `aliasAccessor`, so the walk never descends an `[any]` edge | no |
| every `InitialFactAp.readAccessor` (AP:65-69) | strict literal head match, no `getChild`, no covering arm | no — premise side cannot materialise anything |

**One other site has the pattern.** `Cleaner.cleanConcrete` reads and re-prepends the same accessor
nine lines apart, with no `startsWithAccessor` guard on that path:

```kotlin
// taint/Cleaner.kt:209-214
val child = readAccessor(head)
    ?: return CleanResult(listOf(this), removedAlternative = false)

val remaining = listOfNotNull(clearAccessor(head))
val cleanedChild = child.clean(cleaner.removePrefix(head))
val restoredChildren = cleanedChild.survivingFacts.map { it.prependAccessor(head) }
```

For a fact `x.[any].*` and a cleaner whose head `f` is covered, `readAccessor(f)` matches through the
covered arm and `prependAccessor(f)` yields `x.f.[any].*` — the same hidden unroll.

**It is the same bug class with a much smaller lever**, and it does not change the plan: prefix growth
there is bounded by the cleaner rule's path length (`cleaner.accessors()`), so it cannot iterate the
way summary application can. It is listed here so it is not mistaken for a clean bill of health, and
it is deferred to §13 step 6 rather than bundled — the absorbing primitive of §6.3 applies unchanged
if measurement shows it matters.

This corrects an earlier draft of this document, which proposed charging every fact-producing read.
That would have been both wrong and expensive: it charges rebasing reads that grow nothing, and it
cannot be expressed as an absorption because the two halves are not co-located.

**It also revises the diagnosis of why `saloed/30` failed.** Not "it plugged one of two channels" —
the channel it plugged was the right one. It charged the wrong *counter*: a per-`(entry point, base)`
budget dominated by the unroller, so the refusals fired in the wrong places. The two channels that
matter are the TIFA unroll (§5) and this one, and both are charged here.

### 6.1 The current body

AT:1707-1751, abridged:

```kotlin
fun filterStartsWith(accessPath: AccessPath.AccessNode?): AccessNode? {
    if (accessPath == null) return this
    if (!containsAnyInThisOrDeepNodes && maxDepth < accessPath.size) return null

    val parentAccessors = IntArrayList()
    var filteredTreeNode = this
    var currentApNode: AccessPath.AccessNode = accessPath

    while (true) {
        val accessor = currentApNode.accessor
        filteredTreeNode = when (accessor) {
            FINAL_ACCESSOR_IDX -> { if (!filteredTreeNode.isFinal) return null; manager.finalNode }
            else -> filteredTreeNode.getChild(accessor)?.also { parentAccessors.add(accessor) } ?: return null
        }
        currentApNode = currentApNode.next ?: break
        if (!filteredTreeNode.containsAnyInThisOrDeepNodes && filteredTreeNode.maxDepth < currentApNode.size) return null
    }
    return parentAccessors.foldRight(filteredTreeNode, ::create)     // :1750 -- raw create, no rules
}
```

Line 1750 folds through the **private** `create(accessor, node)` (AT:2194), which enforces only the
taint-mark-leaf rule — no cycle collapse, no element limit, no `[any]` collapse. That is the rebuild
that grows the prefix.

### 6.2 Classifying the descent step

Each `getChild` step is either

- **consuming** — it matched an explicit child edge labelled `accessor` (AT:529), or a child of the
  `[any]` node hoisted up (AT:534), or matched through `.*` (which records `accessor` in the
  exclusion set, so the same step cannot repeat); or
- **non-consuming** — it matched *only* through the `isCoveredByAny` arm (AT:537-541): the node has
  an `[any]` child, has **no** explicit child for `accessor`, and `accessor` is covered. The arm
  returns the `[any]` subtree re-prepended with `[any]`, i.e. the node **unchanged**.

Only the non-consuming case is charged. Where the `[any]` arm *merges* with an explicit child the
step is also consuming and is **not** charged — charging only pure covered reads is the
conservative-for-cost choice and matches where the growth was measured. §13 R6 covers being wrong
about that.

No change to `getChild`'s hot path is needed. The test is the same one `addParentAbsorbingAny` makes
in §6.3 — *does the node reached at this step carry an `[any]` at its root* — evaluated with
`getNodeByAccessor` (AT:496-497), the raw lookup with no `[any]` synthesis: a binary search on the
sorted `accessors` array, the same cost `getChild` already pays.

Any coverage query added here **must** use the guarded idiom of §5.4:
`AnyAccessorUnrollStrategy.AnyAccessorDisabled.unrollAccessor` throws, and it is installed for the
whole prescan phase.

### 6.3 The rule: absorb the prepend, do not truncate the tree

Thread a local `budget`, seeded from the root's limit. At each **non-consuming** step:

- `budget > 0` → `budget--`, descend and rebuild as today;
- `budget == 0` → do not fold this accessor back on. **Absorb it against the `[any]` it was read
  through.**

Absorbing is sound because `X.[any]` already denotes `X.f.…` for every covered `f`, so declining to
write `f` above it asserts more, not less — the same "monotone coarsening" argument
`absorbCoveredByAnyPrefix` makes for itself (AT:847-875).

#### The naive form is unsound, and the trap is worth naming

The obvious implementation — stop the descent and return the node unchanged — is **wrong**. The node
reached by `getChild` is generally a *merge*, not a bare `[any]` subtree:

```kotlin
// AT:534-541
val anyChild = anyAccessorNode.getNodeByAccessor(accessor)
var resultNode = mergeAddMaybeNull(anyChild, node)          // <-- concrete branches are in here too
if (manager.isCoveredByAny(accessor)) {
    ...
    resultNode = mergeAddMaybeNull(originalAnyNoRepeats, resultNode)
}
```

Dropping the prepend across the whole merged node would rewrite `a.f.S` as `f.S` on the concrete
branches — **neither a superset nor a subset**, so a genuine loss. The absorption has to **split**:
skip the step only on the `[any]`-rooted branch, and keep it on everything else.

```kotlin
/**
 * Prepend [accessor] above this node, EXCEPT on the branch an `[any]` at this node's root already
 * denotes. `a.[any].R` is a subset of `[any].R` for covered `a`, so dropping the step there is a
 * monotone coarsening. Every other branch keeps the step: `a.f.S` and `f.S` are disjoint.
 */
private fun addParentAbsorbingAny(accessor: AccessorIdx): AccessNode {
    if (!manager.isCoveredByAnyOrFalse(accessor)) return create(accessor, this)
    val anyNode = getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return create(accessor, this)

    val absorbed = create(ANY_ACCESSOR_IDX, anyNode)                 // [any] branch, step skipped
    val rest = clearChild(ANY_ACCESSOR_IDX).takeIf { !it.isEmpty } ?: return absorbed
    return create(accessor, rest).mergeAdd(absorbed)                 // everything else keeps it
}
```

All four primitives it uses already exist: `getNodeByAccessor` (AT:496), `clearChild` (AT:952),
`mergeAdd` (AT:1134), `create` (AT:2194). `:1750` becomes

```kotlin
return parentAccessors.foldRight(filteredTreeNode) { a, node -> node.addParentAbsorbingAny(a) }
```

and because `foldRight` is innermost-first and the result keeps `[any]` at its own root, the
absorption **chains** up a run of covered steps — which is what makes `f.g.[any].*` collapse to
`[any].*` rather than only shaving one link.

#### No existing primitive expresses this

Checked, and none of the four does:

| primitive | what it does | why it does not fit |
|---|---|---|
| `prependAnyAccessor` AT:772-808 / AP:609-644 | the `X.[any].f.[any] → X.[any]` invariant | only absorbs when the accessor **is** `[any]` |
| `absorbCoveredByAnyPrefix` AT:847-908 | pulls a covered prefix *up out of* a delta grafted under an `[any]` | requires an `[any]` edge **above**; run here it would consume the `[any]` we are trying to keep |
| `trimAnyCoveredAndPushChildren` AT:1291-1329 + `AccessTreeAnySuffixMatcher` | merge-time fold of `[any].S ∪ x.y.S` | operates on merge operands, not on a prepend |
| `addParentIfPossible` AT:546-579 | the legality/normalisation gate | its `[any]` arm fires only for `accessor == ANY_ACCESSOR_IDX`; for a covered field it takes `addParentFieldAccess` and unconditionally builds `a.[any].…` |

#### Proxy vs. exact test

`addParentAbsorbingAny` tests *"the accumulator carries an `[any]` at its root"*, which is a **proxy**
for *"`getChild` matched this step through the covered arm"*. They diverge when the fact had a genuine
concrete child at that level **and** an unrelated `[any]` sibling: the proxy then absorbs a step that
was actually consumed, costing precision (never soundness).

The codebase already has the exact idiom — `parentEdgeIsAny` (AT:1646, :1662, :1690): derive the flag
from the edge just traversed, thread it exactly one level, never inherit. Applying it here means
having `getChild` report whether the AT:537-541 arm contributed, and recording that per element of
`parentAccessors`. **Start with the proxy**; §12.2's superset check will show whether the imprecision
is visible, and the exact form is a drop-in refinement of the same split primitive.

#### What stays raw

The `rest` branch keeps the raw `create`, not `addParentIfPossible`. Switching it would newly apply
`limitFieldAccess` / `limitElementAccess` to the rebuilt spine — a behaviour change pinned by
`AnyAccessorPremiseTest.kt:187` (`limitFieldAccess does not collapse across an any`). Out of scope
here; note it as a separate question.

### 6.4 Consumers, and what the tests say

The three consumers pair the filtered node with a separately-stored caller initial AP and rebuild the
wrapper downstream — none of them appears to require structural prefix-equality:

```kotlin
// SUB:87-88   (ND collect)
val filteredExitAp = current?.filterStartsWith(summaryInitialFact) ?: return; dst.add(filteredExitAp)
// SUB:180-183 (F2F find)
val filteredExitAp = callerExitAp.filterStartsWith(summaryInitialFact) ?: return@forEach
dst.add(filteredExitAp, storageInitialFacts[storageIdx])
// SUB:310-311 (Z2F find)
callerPathEdgeFactAp?.filterStartsWith(summaryInitialFact)?.let { dst += ZeroEdgeSubBuilder(apManager).setNode(it) }
```

**This remains the one assumption that must be verified before implementation** (§12.2, R1). It is
weaker than it was, because absorption returns a fact that still starts with the premise in the
covered sense rather than a truncated one — but it is still an assumption.

Existing tests that constrain the change:

| test | pins |
|---|---|
| `AnyAccessorCollapseTest.kt:194` — `filterStartsWith matches a premise longer than the any depth charge` | the two `containsAnyInThisOrDeepNodes` prefilters must keep matching a 16-link premise against `base.[any].*`. **Asserts non-null only, not shape** — so it will not catch an absorption regression, and a shape-asserting test must be added |
| `AnyFieldMarkExclusionTest.kt:318` — `an abstract node under a field under an any must not absorb` | the soundness boundary: only the *immediate* parent edge licenses absorption. The split in `addParentAbsorbingAny` is what respects it |
| `AnyAccessorCollapseTest.kt:116`, `AnyAccessorPremiseTest.kt:102` | the `X.[any].f.[any] → X.[any]` rule, fact and premise sides |
| `AnyAccessorPremiseTest.kt:211` | `size` is the literal link count and `depth` charges `[any]` at 10 — the prefilters compare `maxDepth` against `AccessPath.size`, so neither may be disturbed |
| `AccessBasedStorageAnyLookupTest.kt:112-347` | the **pull** path's `[any]` lookup. `AccessBasedStorage.kt:67-70` states pull and push are expected to agree, so changing the push path is worth re-checking against these |

---

## 7. Storages and joins

### 7.1 There is no fact *set* — there is a tree join

This reframes the original sketch. Every storage slot holds exactly **one** `AccessNode`, and
"adding a fact" is a structural join:

```kotlin
// MethodEdgesFinalTreeApSet.kt:32-40
val mergedFacts = factSet.mergeAdd(accessPath)
if (mergedFacts === factSet) return null          // <-- "already subsumed", by REFERENCE
edges[factSetIdx] = internIfRequired(mergedFacts)
```

and `null` means *do not propagate*:

```kotlin
// MethodAnalyzerEdges.kt:70
val addedAp = storage.add(edge.statement, edgeAp) ?: return emptyList()
```

So today, a fact that "already exists" is discarded whole and propagation stops. **That is exactly
the failure mode the design must prevent**: a fact that already exists but arrives with *more* budget
must still make progress.

### 7.2 Why the storage rule is min, and why that is forced

Because a slot holds **one merged tree**, and that tree represents *both* facts. When it grows, it
grows the union — including the component that only had budget 2. A single tree therefore carries a
single budget, and that budget has to be safe for everything the tree denotes:

> `limit(merge(a, b)) = min(limit(a), limit(b))`

Taking the max would let the low-budget component ride the high-budget component's budget, which is
exactly the "fresh budget per fact" failure mode. **min is not a preference here; it is forced by the
representation.** The same argument makes min right at every other meet (P3, P5, P6): there is never
a moment where two budgets coexist in one object.

It is also the sound direction. A lower limit means more collapsing to `[any]`, i.e. a coarser fact,
i.e. an over-approximation (§9.2). So "when in doubt, take the lower budget" and "when in doubt, be
sound" are the same instruction.

### 7.3 The single hook, and what counts as a change

Both merges funnel through `mergeNodeLoop` (AT:1231). Put the rule in the two step functions,
alongside the existing `isAbstract = this.isAbstract || other.isAbstract`:

- `mergeAddStep` (AT:1145-1170) — `limit = min(this.limit, other.limit)`;
- `mergeAddDeltaStep` (AT:1178-1229) — the same.

That covers all eleven join call sites at once: `MethodEdgesFinalTreeApSet.kt:32`,
`MethodEdgesInitialToFinalTreeApSet.kt:98`, `MethodEdgesNDInitialToFinalTreeApSet.kt:30`,
`MergingTreeSummaryStorage.kt:24,43`, `MethodNDInitialToFinalApSummaries.kt:58,62`, `SUB:77,148,298`,
`TIFA:414`.

**A limit-only decrease must NOT count as a delta.** This is the one subtlety, and it has two
defensible answers.

The existing guards (AT:1158-1165, AT:1212-1218) return `this` by identity when the shape is
unchanged, and the storages turn that into "do not propagate" (`MethodAnalyzerEdges.kt:70`). Since the
limit lives on an immutable node, a lower limit means a *different node object*. If the guards learned
about the limit, that would read as a change and re-propagate the whole subtree — re-deriving, at
budget 2, work already done at budget 5 whose results subsume it. Pure waste. So the guards stay keyed
on **shape only**, either way.

| | (i) **drop the lowering** | (ii) **install it in the slot** |
|---|---|---|
| what happens | the guard returns `this`; the lower limit is discarded | the guard still returns "no progress", but the slot's reference is replaced with the min-limit root |
| cost | zero | one root-node allocation per lowering |
| bound | weaker — a shape can keep a higher limit than some derivation justifies | enforced: the cut bites on every subsequent read of that slot |

```kotlin
// (ii), sketch at MethodEdgesFinalTreeApSet.kt:32-40
val mergedFacts = factSet.mergeAdd(accessPath)          // shape merge, limit min-ed inside
if (mergedFacts.sameShapeAs(factSet)) {
    edges[factSetIdx] = mergedFacts                      // keep the tighter limit
    return null                                          // but report no progress
}
```

Nothing is mutated in (ii) either: the node is immutable, the array slot is not, and slots are already
rewritten on every merge (`edges[factSetIdx] = internIfRequired(mergedFacts)`).

**Take (ii).** Enforcing the bound is the entire point of choosing min, and the cost is one node —
the root — not a tree. But instrument it: §11's diagnostics must count lowerings, because §3.5 argues
they should be *rare* (on the dominant channel the limit is already a function of the shape). If the
counter is near zero, (i) and (ii) are the same thing and the allocation is free; if it is large, that
is a signal the design's model of where budgets diverge is wrong, and worth knowing before §12.3.

Consequences of min being monotone downward, all of them good: no retraction machinery, no
re-propagation, no `|nodes| × L` term. The budget assignment converges because it can only fall, and
it is bounded below by 0.

Note interners are **per-storage**, not global (`TreeSetWithCompression.kt:10`,
`MergingTreeSummaryStorage.kt:13`, `SUB:26`, `TreeFinalFactList.kt:24`, `TIFA:36`), so limits are
tracked per node object rather than globally per shape — finer, and with less cross-contamination
between unrelated parts of the analysis.

### 7.4 The per-base aggregate is an index, not a source of budget

Maintain, per `(storage, AccessPathBase)`, `maxLimit = max` over the entries. Note this is a `max`
*over* the min-combined per-fact limits — a different thing from the combining rule, and its **only**
legal use is early exit:

> if `maxLimit == 0`, no fact under this base can spend — skip the unroll machinery entirely.

Read this way the aggregate is a pure optimisation: `max` is the safe direction for it (too high only
costs a wasted check), and it has no effect on results.

**A fact must never read its budget from the aggregate.** That would re-introduce exactly the
context-keyed counter §1 removes, and break I1 — one permissive fact would refresh every fact under
the base and the chain bound would be lost. This is a deliberate narrowing of the original sketch:
the aggregate is kept, its authority is not.

`AccessPathBase` resolution is already O(1): the `CommonInst` is resolved once at storage
construction into `method.parameters.size`, and every lookup is a `when` over a sealed class with
direct field access (`AccessPathBaseStorage.kt:36-44, 62-70`) — `Argument(idx)` is one array index.

### 7.5 Four places the limit is destroyed and must be re-applied

| # | site | what happens |
|---|---|---|
| D1 | `markInterned` AT:1494 | rebuilds through the private ctor; already does not copy `anySuffixMatcher`. Must copy the limit. |
| D2 | `filterStartsWith` AT:1750 | rebuilds with the raw `create`. §6.3 sets it explicitly. |
| D3 | `MergingTreeSummaryStorage.compressNode` `:59-73` | `removeAllAccessorChains` pulls subtrees up and merges them; **the new root is not the old root**. Re-apply at `MergingTreeSummaryStorage.kt:34-36`. |
| D4 | `MethodInitialToFinalApSummaries` id-edge `:151-157` | synthesises the final **from the premise** — no incoming fact at all. The limit must be derived from the premise or stored beside the `ExclusionSet` at `:159`. |

Also: `Serializer.writeAccessNode` AT:1942 / `readAccessNode` AT:1976 use a 3-bit wire mask
deliberately decoupled from `flags` (AT:1943-1945). A field not added there resets to its default on
every summary round-trip — see §13 R7.

---

## 8. Two things this design must not collide with

### 8.1 Premises do not carry a limit

`AccessPath` (the premise) is a chain, and premises never spend: the budget rides the fact. The one
place this shows is D4 above, where a summary's final is synthesised from its premise.

The `[any]` premise emitted on exhaustion (§5.2) is likewise unbudgeted — it is the *coarse* answer,
the terminal state, and nothing derived from it can spend more.

Consequently the limit goes on `FinalFactAp`, not on the shared `FactAp` supertype — putting it on
`FactAp` would force the premise side to answer, and the generic `<F : FactAp>` mappers
(`JIRMethodCallFactMapper.kt:132-139, 210-216`, `GoMethodCallFactMapper.kt:36-40, 114-119`) would then
need a meaningless premise limit.

### 8.2 The existing depth gate needs no change, and the two do not fight

```kotlin
// MethodAnalyzer.kt:591-595
private fun edgeExceedLimit(edge: FactToFact): Boolean {
    if (edge.initialFactAp.depth > factDepthLimit) return true
    if (edge.factAp.depth > factDepthLimit + 2) return true
    return false
}
```

Delay plus iterative deepening keeps working as-is. Three observations, none of them requiring a
change:

**(a) The two mechanisms pull the same way.** `edgeExceedLimit` gates on *depth*, and a limit refusal
produces a **shallower** fact — `arg0.p.[any].*` instead of `arg0.p.f.[any].*`. So a refused fact is
*more* likely to clear the gate, not less. There is no interaction to defend against: the refusal
happens inside the tree operation, before any edge exists, and what reaches
`delayedF2FInitialEdges` / `delayedF2FSummaries` (`MethodAnalyzer.kt:559-567`, `:700-707`) is an
ordinary edge that the growing `factDepthLimit` (`:573-589`) admits in the normal way.

**(b) A measurement caution, not a design constraint.** `ANY_ACCESSOR_DEPTH_CHARGE = 10` (AT:2057)
against `INITIAL_ALLOWED_FACT_DEPTH = 3` (`MethodAnalyzer.kt:1390`) means a single `[any]` costs
`10 > 3+2`, so an `[any]`-carrying F2F edge is delayed on first sight and admitted only after the
unit has climbed the resume ladder (`TaintAnalysisUnitRunner.kt:351-362`) a few times. That is
iterative deepening doing its job, but it means a sweep arm must run long enough for the ladder to
climb before its `rc`/premise count is read — otherwise a run that was merely early gets scored as
converged, or vice versa. §12.3 notes it.

**(c) The gate never sees a freshly-minted source fact.** `edgeExceedLimit` takes `FactToFact`;
`delaySummaryEdge` returns `false` for anything else (`:701`), and `addInitialZeroToFactEdge`
(`:545-548`) goes straight through. Source-born facts arrive as `ZeroToFact` (§4.1 M1), so the
per-fact limit is the *first* mechanism to constrain that class of fact. The two cover disjoint edge
kinds rather than overlapping ones.

---

## 9. Correctness

### 9.1 Termination

By I2 every budget originates at `L`. By I1 — which min makes global, not merely per-chain — no
operation anywhere raises a limit. By P8 every growth step strictly decrements one.

A fact reached by a derivation containing `k` growth steps therefore has budget at most `L − k`, and
no fact with `k > L` is reachable by any route. **The number of concrete links accumulable above an
`[any]` is bounded by `L`.** With accessors finite per program point, the reachable shape set is
finite.

Min makes this argument shorter than it would otherwise be: because limits only fall, there is no
need to reason about which derivation reached a shape first, no fixed-point iteration over budgets,
and no bound of the form `|nodes| × L` on re-propagation work. The budget assignment converges
trivially — it is monotone decreasing and bounded below by 0.

What this does *not* bound: legitimate deep chains from ordinary field reads, which are consuming and
cost nothing. The no-`[any]` control converged at 13 links. The bound applies only to links bought
with an `[any]`.

### 9.2 Soundness

Both exhaustion behaviours replace a fact with a **superset**:

- §5: `[any]` stays un-unrolled — `X.[any]` ⊇ `∪ᵢ X.aᵢ.[any]`.
- §6: the un-grown tree — `arg0.p.[any].*` ⊇ `arg0.p.f.[any].*`.

Under the universal reading of `[any]` ("every suffix below here is tainted", per the `[any]`-premise
design §1) both are over-approximations. Over-approximating taint can add false positives; it cannot
drop a true flow. So **no value of `L`, including `0`, can lose a finding relative to `L = ∞`** — a
property the current per-context cap does *not* have (cap 0 lost findings even when it completed).

That claim is sharp and falsifiable. §12.3 tests it directly.

### 9.3 Determinism, honestly

Min without retraction is **order-sensitive in precision**. A shape reached first at budget 5
propagates children at 5; if the budget-2 derivation had arrived first, those children would never
have existed. Nothing retracts them, so the fact set depends on arrival order.

**The schedule does vary between runs.** This was checked rather than assumed, and the answer is not
the comfortable one:

- Analysis is multi-threaded by default and there is no knob —
  `newFixedThreadPoolContext(nThreads = (availableProcessors() / 2).coerceAtLeast(1))`
  (`TaintAnalysisUnitRunnerManager.kt:91-96`), one runner coroutine per unit, units being packages.
  Cross-unit facts are injected into another runner's channel *from the calling thread*.
- The per-unit `PriorityQueue(EventComparator)` (`TaintAnalysisUnitRunner.kt:74`) is not a stable
  order: `EventComparator` ends in a `.sign` that returns 0 on ties, its ordering keys
  (`analyzerSteps`, `containsUnprocessedZeroToZeroEdges`) **mutate while elements sit in the heap**,
  and the batch boundary is `tryReceive`, i.e. whatever has arrived.
- Accessor indices are assigned in first-encounter order by a process-wide interner
  (`AccessorInterner.kt:24-35`) hit concurrently by every runner, and those indices key open-addressed
  `Int2ObjectOpenHashMap`s whose iteration order therefore varies — and that order drives premise
  generation in `AccessBasedStorage` (`:145-156`, `:167`, `:191`), not just printing.

**And the variation is live, not theoretical.** Across ten same-config runs the
`unvalidated-redirect-in-spring-app` codeFlow flipped between `MiscUtils.java:91` and `:94`, with
three distinct trace hashes inside one arm. The schedule demonstrably moves; it simply has not yet
moved a finding *endpoint*.

Three things still bound the exposure:

1. **It cannot change soundness.** Every reachable budget assignment is a valid over-approximation
   (§9.2), so order can move the false-positive count, never the true-positive set.
2. **It is not new.** `unrolledFactCount` is already a sticky, order-dependent cut, and the code says
   so (TIFA:395-401). This design moves order-sensitivity from a per-base counter to a per-fact one.
3. **Findings have been stable in practice.** The CI gate
   (`.github/workflows/ci-analyzer-owasp.yaml`) asserts an *exact* trace total (`EXPECTED_TRACES:
   2633`) on OWASP BenchmarkJava on every push to main, and has survived as a merge gate.

But (2) cuts both ways, and this is the honest cost of choosing min: a per-fact cut **binds far more
often, and much closer to the hot path**, than a per-base one. That is a real increase in exposure,
not a wash.

**Why park-and-replay is not available here.** The engine already contains an order-*independent*
resource cut — `factDepthLimit`, which parks over-limit edges (`MethodAnalyzer.kt:560-566`) and
replays every one of them when the limit rises (`:573-589`). That idiom works because the limit
*rises*. Under min the budget only ever falls, so a parked edge would never be admitted and there is
nothing to replay. Ordering-independence would require either §10's structural measure — a pure
function of the shape, and therefore order-free by construction — or inverting the design into a
global deepening ladder on `L`, which is a different design, not a tweak to this one.

**Validation obligation, and it is sharper than it looks.** §12.6 runs the same project twice and
diffs. It must diff the **whole SARIF including `codeFlows`**: the usual `findings.tsv` digest is
provably blind to this, because `SarifGenerator.computeFingerprint` uses `FingerprintKind.SOURCE_SINK`
with only `trace.firstOrNull()` (`SarifGenerator.kt:139-146`, `:159`) — precisely the granularity at
which variation has already been observed.

---

## 10. Alternatives considered

### 10.1 A structural measure

Worth recording, because it is dramatically cheaper and survives if §12.1's heap gate fails. It gets
*more* attractive under the immutability and min constraints, not less: a pure function of the tree
needs no field, no constructor plumbing, no interner question, no serializer change, and no
combining rule at all — the whole of §3 and §7 evaporates.

Define, as a pure function of the tree, `anyPrefixDepth` = the number of concrete links from the root
to the **shallowest** `[any]` node. Refuse the covered-read prepend when `anyPrefixDepth ≥ L`.

| | carried limit (this design) | structural measure |
|---|---|---|
| storage | one byte per node, + interner/serializer discipline | **none** |
| determinism | order-sensitive (§9.3) | **free** — a function of the shape, so order cannot reach it |
| termination | `L` decrements per chain | reachable shapes have `anyPrefixDepth ≤ L` |
| combining rule | min at every meet (§4, §7) | none needed |
| in `filterStartsWith` | thread a budget | already known: `parentAccessors.size` at the `[any]` |
| distinguishes provenance | **yes** | **no** — penalises a deep concrete chain that merely *ends* at an `[any]` |

The last row is the whole argument for the carried limit. Whether it matters is measurable: the
no-`[any]` control reached 13 concrete links, so an `L` above that would leave legitimate chains
untouched under either scheme, and the two designs would differ only on facts that mix deep concrete
prefixes with `[any]`.

**Recommendation: build the carried limit as specified; run §12.3's sweep with the structural measure
as a second arm.** It costs one extra arm and it either justifies the byte or retires it. The two also
compose — carry the limit where provenance matters (TIFA) and use the structural measure where it does
not (`filterStartsWith`) — but only pursue that if the sweep says they differ.

### 10.2 A global deepening ladder on `L`

Not recommended, but recorded because it is the only route to order-independence that keeps the
carried limit, and because the engine already contains a working instance of the pattern.

`factDepthLimit` is order-independent precisely because it *rises*: over-limit edges are parked
(`MethodAnalyzer.kt:560-566`) and every one is replayed when the limit goes up (`:573-589`). The
analogue here would start at `L = 0` — maximally coarse, guaranteed to converge — and deepen `L`
globally, replaying refused work each time, until the budget or the clock runs out.

Why it is not the proposal: it inverts the design rather than adjusting it. The per-fact budget would
become a *parking key* instead of a cut, every refusal would have to be recorded and replayable, and
the coarse-fact-on-exhaustion behaviour of §5 and §6 — which is what makes exhaustion sound — would
have to be replaced by parking. That is a larger change than this document scopes, and it should only
be reached for if §12.6 shows the order-sensitivity actually moves findings.

---

## 11. Configuration

| property | meaning | default |
|---|---|---|
| `opentaint.anyUnrollLimit` | `L`, the mint value. `< 0` = unbounded (today's semantics) | chosen by §12.3 |
| `opentaint.anyLimitDiag` | counters: mints by site, decrements, refusals, **lowerings dropped vs installed** (§7.3), interner variants per shape (§3.5), aggregate early-exits | `false` |

Restore the property read at TIFA:517-518, currently hard-wired to `100` with `System.getProperty`
commented out. Both the KDoc at TIFA:505-516 and the comment at `DefaultConfiguration.kt:64` claim
the cap is off by default and read from a property; **both are now false** and should be corrected as
part of this work. `opentaint.anyUnrollLimit` is already in `FORWARDED_TEST_PROPERTIES`
(`DefaultConfiguration.kt:65`); `anyLimitDiag` must be added.

`L < 0` must reproduce today's behaviour **exactly** — no field reads, no joins, no refusals — so the
feature is one flag away from off.

---

## 12. Validation

### 12.1 Heap — gates everything (§3.2, §3.5)
Two checks. First, that `L ≤ 7` in `flags` bits 5-7 costs **zero bytes** — verify with JOL that
`AccessNode`'s size is unchanged, and that with `L < 0` the `flags` byte is bit-identical to today.
Second, that identity-inclusive limits do not inflate the node population: node count and peak RSS on
conductor and thingsboard, at `L < 0` versus the chosen `L`. The §3.4 canonicalisation predicts inflation confined
to `[any]`-bearing nodes; a regression beyond noise means the gate is not doing its job and §10.1
becomes the design.

### 12.2 The consumer contract — gates §6
The one load-bearing assumption. Force the §6.3 refusal on *every* non-consuming step (i.e. `L = 0`
on that path only) and assert the three consumers in `MethodTreeAccessPathSubscription` produce a
**superset** of the baseline SARIF on openmrs and tms. Any *lost* finding refutes §6.4 and selects the
fallback.

### 12.3 Soundness and the choice of `L`
Sweep `L ∈ {0, 1, 3, 10, 100, ∞}` on openmrs, tms, thingsboard, conductor, plus the §10 structural
measure as a control arm. Record `rc`, wall, peak RSS, premise count, SARIF set, and — per §8.2(b) —
the final `factDepthLimit` the resume ladder reached, so an arm that was merely early is not scored
as converged.

**The prediction to state before the run:** every finite `L` must produce a **superset** of `L = ∞`'s
findings, and conductor must reach `rc = 0` at some finite `L`. If a finding present at `L = ∞` is
absent at a finite `L`, §9.2 is wrong and this needs rework, not tuning.

Then choose the smallest `L` that converges conductor and leaves openmrs/tms/thingsboard
SARIF-identical.

### 12.4 Other backends
**The cactus backend does not have this bug**, which is worth stating because it looked like it did.
Its `getChild` (`AccessCactus.kt:554`) is a plain edge lookup with no `isCoveredByAny` arm —
`anyAccessorUnrollStrategy` is stored by `CactusApManager` and never consulted anywhere in the
package — and its `filterStartsWith` (`AccessCactus.kt:1010`) rebuilds from the *query*
(`createAbstractNodeFromAp` + `concatToLeafAbstractNodes`) rather than folding the walk history back
on. So `readAccessor(a).prependAccessor(a)` is an exact round-trip there, and the `Cleaner.kt` sites
are benign on cactus too.

Consequence: cactus needs no change, but it also cannot serve as a control for this design — the two
backends differ in the mechanism under test, not just in representation.

### 12.5 The gate
`core/`'s bare `gradlew test` does **not** reach `opentaint-dataflow-core` — it is an included build,
and a bare `compileTestKotlin` does not reach its test source set either. Name tasks explicitly.
Baselines: 212 (opentaint-dataflow), 735 (core root), 3405 (full gate).

### 12.6 Run-to-run stability — gates §9.3
**This has never been run**: there is no CI job and no in-repo harness that analyses the same project
twice and diffs. Three requirements, each of which the obvious version of this check gets wrong:

- **Diff the whole SARIF including `codeFlows`.** The usual `findings.tsv` digest is blind to the
  variation already observed, because its fingerprint uses only `trace.firstOrNull()`
  (`SarifGenerator.kt:139-146`, `:159`).
- **Pick a project that converges**, and raise the timeout if needed. Timeout-bound runs are not
  reproducible even in principle — the phase budgets are derived from *measured elapsed time*
  (`TaintAnalyzer.kt:137`, `:156`) and a memory-pressure detector can cancel the run. Same-jar
  conductor pairs already differ in progress (2,528,446 vs 2,491,067), so conductor cannot answer this
  question, only muddy it.
- **Land the interner race fix first** (R11). A wrong accessor index is a shorter route to divergent
  findings than schedule order, and it would contaminate the measurement.

A clean pass means min's order-sensitivity is theoretical and §9.3 is a footnote. A difference means
the finding set is run-dependent and must be surfaced before shipping — every other arm in §12 is
judged by SARIF comparison, so a moving baseline invalidates them all.

---

## 13. Implementation plan

Ordered so each step is separately testable; steps 1–2 are inert by construction.

1. **The field** — `anyLimit` as an immutable `Byte`, no constructor default; the §3.4 `⊤`
   canonicalisation in the init block; `InternStrategy.equals` only (**not** `hash`, **not**
   `AccessNode.equals` — §3.3); `markInterned` copies it; the wire mask bits 3-5 (§3.7); `L` from the
   property. Nothing reads it yet.
   *Gate: full suite green; §12.1; and with `L < 0` every node is `⊤`, so behaviour is unchanged by
   construction.*
2. **P1–P7 propagation**, including the four D-sites of §7.5, the §3.4 `[any]`-introducing-prepend obligation, and the 14 call sites of the general builder (§3.6).
   *Gate: a property test asserting I1 over random operation sequences.*
3. **§7.2-7.3 the min rule at the merges** — applied at the root, outside `mergeNodeLoop`, plus the
   shape-only change guard so a limit-only decrease does not re-propagate.
   *Gate: a test that a same-shape fact arriving with a LOWER limit tightens the slot without
   re-propagating, and that the merged tree's root carries the min.*
4. **§5 TIFA spend** — the per-frontier latch (§5.3a), the explicit refusal signal (§5.3b), the
   coarse pair on exhaustion. *Gate: `AnyPremiseAbstractionTest` extended with per-fact-budget cases.*
5. **§6 `filterStartsWith` spend** — `matchedOnlyThroughAny` with the guarded coverage idiom (§5.4),
   the budget thread, the absorbing early return. *Gate: a unit test pinning the fixed point —
   `arg0.p.[any].*` at limit 0 against `arg0.p.f.*` returns itself.*
6. **`Cleaner.cleanConcrete`** (§6.0) — the second read+prepend site, same primitive. Land only if
   §12.3 shows it matters; its lever is bounded by the cleaner rule's path length.
   *Gate: `FactCleanerContractTest` and the cleaner analysis tests stay green.*
7. **§7.4 per-base aggregate** — optimisation only; land last, measure separately.

---

## 14. Risks

| # | risk | severity | mitigation |
|---|---|---|---|
| R1 | §6.4 is wrong — a consumer needs structural prefix-equality | **high** — redesign, not a tweak | §12.2 checks it before step 5; §6.4's fallback costs one extra link per chain |
| R2 | Interner fragmentation inflates the node population, or the identity-keyed merge memo misses per variant and costs CPU (§3.5) | **high** — heap is the binding constraint | §3.4's `⊤` canonicalisation confines it to the `[any]` spine, bounded at `L+1` variants per shape; §12.1 measures node count and peak RSS. If it still bites, §10.1 replaces the design rather than patching it |
| R3 | The per-frontier latch (§5.3a) burns the demand memo in a new way | medium | the memo is one-shot and irreversible; needs a dedicated test asserting a refused frontier does **not** consume `unrolled` |
| R4 | `L > 7` turns out to be needed, exceeding the 3 free wire-mask bits (§3.7) | low | the in-memory `Byte` handles up to 127; only serialization is capped. §12.3 reports whether the useful `L` is at the ceiling; if so, a version tag becomes a prerequisite |
| R5 | `L` small enough to converge conductor is coarse enough to add FPs elsewhere | medium | §12.3 requires openmrs/tms/thingsboard SARIF-identical at the chosen `L` |
| R6 | The proxy test in `addParentAbsorbingAny` (§6.3) absorbs a step that was genuinely consumed, when a concrete child and an unrelated `[any]` sibling coexist | low — costs precision, never soundness | §12.2's superset check surfaces it; the exact `parentEdgeIsAny`-style form is a drop-in refinement of the same split primitive |
| R7 | A stale gzipped summary from a previous run is read back with a wrong limit | low **given the bias**, catastrophic without it | §3.7: there is **no version tag anywhere** on this path and `loadSummaries` validates nothing, so the encoding must stay byte-width-preserving and bias `0` to mean `⊤`. Any byte-adding encoding needs a version tag first |
| R8 | `AnyAccessorDisabled` throws on the new coverage query during prescan | low but total (analysis stalls) | §5.4 mandates the guarded idiom; this bug has already been hit once |
| R9 | `Cleaner.cleanConcrete` (§6.0) is left uncharged and keeps growing prefixes | low — its lever is bounded by the cleaner rule's path length, so it cannot iterate | deferred to step 6; §12.3 shows whether it matters |
| R10 | An arm is scored before the resume ladder has climbed, so a merely-early run reads as converged (or the reverse) | medium — a measurement error, not a design fault | §8.2(b): every sweep arm runs to the same wall-clock budget and records the ladder's final `factDepthLimit` alongside `rc` |
| R11 | The interner data race silently returns a wrong accessor index, diverging findings independently of this design | **high for measurement** | the fix `e082a4b72` is **not** on this branch (`git merge-base --is-ancestor e082a4b72 HEAD` → false). Land it before any §12.6 or §12.3 measurement, or the results are uninterpretable |
| R12 | Min binds per-fact, so order-sensitivity is exercised far more often than the per-base cut it replaces | medium | §9.3 states the cost plainly; §12.6 measures it; §10's structural arm is the order-free fallback if it bites |

---

## 15. What this design does not do

It does not touch the **population** of `[any]` facts, only their ability to grow. The 10 `$*`
whole-object source markers that seed the conductor blow-up (16–37× on their own) are unchanged. If
`L` has to go very low to converge conductor, that is evidence the source rules are the better lever
and this bound is treating a symptom — §12.3's sweep is what tells them apart.

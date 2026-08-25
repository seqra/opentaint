# The `delta` + `concat` round trip: right mechanism, and it is the fallback

Tests a specific hypothesis:

> We have a fact in the call context, like `arg0.[any].*`, and a summary edge `arg0.a.* -> ret.a.*`.
> The delta operation unrolls the `[any]` (read `a`) and concat then prepends an `a`, resulting in
> fact growth.

**Verdict: the mechanism is exactly right, confirmed both by a deterministic unit test and by
verbatim samples from conductor. It is also, in the default configuration, almost never used — it
fires twice in a whole run. It becomes the dominant path only when the `[any]` unroll is refused,
and that is why refusing the unroll makes everything worse.**

---

## 1. The mechanism, exactly as described

`AnyDeltaConcatRoundTripTest`, three tests, all passing:

| test | result |
|---|---|
| `reading a concrete accessor off an any-carrying fact consumes nothing` | the remainder of `arg0.[any].*` against premise `arg0.a` still carries the `[any]` |
| `the round trip returns a fact one concrete link longer, still carrying the any` | `ret.a.*` ⊕ remainder = **`ret.a.[any].*`**, byte-for-byte |
| `the round trip is a ratchet` | four laps: `arg0.[any].*` → **`arg0.a.b.c.d.[any].*`**, depth strictly increasing, `[any]` present at every lap |

Why, from `AccessNode.getChild` — for fact `arg0.[any].*` and accessor `a`:

```kotlin
val node = getNodeByAccessor(accessor)                    // literal child `a`  -> null
val anyAccessorNode = getNodeByAccessor(ANY_ACCESSOR_IDX) // the [any] subtree  -> X
val anyChild = anyAccessorNode.getNodeByAccessor(accessor)// `a` under [any]    -> null
var resultNode = mergeAddMaybeNull(anyChild, node)        //                    -> null
if (manager.isCoveredByAny(accessor)) {
    val anyAccessorNoRepeats = anyAccessorNode.clearChild(accessor)          // X
    val originalAnyNoRepeats = anyAccessorNoRepeats.addParentIfPossible(ANY) // [any] -> X
    resultNode = mergeAddMaybeNull(originalAnyNoRepeats, resultNode)         // [any] -> X
}
```

The arm **rebuilds the edge it just read through** and returns the node it read *from*. The read
consumes a link of the premise and no link of the fact. `concat` then hangs that unchanged remainder
below the conclusion's concrete prefix, so the fact comes out one link longer with its `[any]` intact
— a fixed point with a ratchet.

And it happens on the real workload. Verbatim, from the unbudgeted conductor run:

```
premise   = <this>.workflowDef.*
fact      = <this>.[any]![graaljs…#spring-source].$
remainder = .[any]![graaljs…#spring-source].$          <- identical to the fact
```

`remainderPerFact = 1.00` for both recorded events: the premise consumed nothing at all.

---

## 2. In the default configuration it fires twice

New counters, one endpoint, one rule:

| | manager off (default) | `L=0` |
|---|---:|---:|
| **`delta()` calls that read through an `[any]`** | **2** | **369,633** |
| of those, remainder still carries the `[any]` | 2 (100%) | 146,238 (40%) |
| of those, remainder no smaller than the fact | 2 (100%) | 11,812 (3%) |
| `concat` calls whose delta carries an `[any]` | 14,045 (0.23% of grafts) | **813,094** |
| of those, result still carries the `[any]` | 13,953 (**99.3%**) | 800,798 (**98.5%**) |
| `getChild` `[any]` synthesis calls | 72,538 | **14,919,000** |

**Two.** Out of 11,437,909 `delta()` calls in the unbudgeted run.

The reason is that the `[any]` unroll gets there first. `unrollAnyAccessors` **consumes** the `[any]`:
it materialises `arg0.a`, `arg0.b`, … as *concrete* facts and merges them into `added`, so by the
time a summary premise is matched against a fact, the fact is concrete. Two independent measurements
agree on this: both exact tree dumps in the trace document report **`[any]` edges: 0**, and now the
operation side reports **2** reads through an `[any]` in a whole run.

So the deep concrete chains — `.taskInput.MapValue.tasks.Element.name` and friends — are built by the
unroll re-rooting carriers ([[any-unroll-copies-the-carrier]]), **not** by this round trip.

---

## 3. It is the fallback, and the fallback is worse

Refuse the unroll and the `[any]` has nowhere to go but into the facts, where every read must
synthesise through it:

| | off | `L=0` | ratio |
|---|---:|---:|---:|
| `delta()` through an `[any]` | 2 | 369,633 | 185,000× |
| `concat` with an `[any]`-carrying delta | 14,045 | 813,094 | 58× |
| `getChild` synthesis calls | 72,538 | 14,919,000 | 206× |
| graft points per `concat` | 2.72 | **16.47** | 6.1× |
| nodes created per `concat` | 25.03 | **99.69** | 4.0× |
| distinct nodes created per `concat` | 10.32 | 27.47 | 2.7× |
| IFDS progress | 2,444,281 | 742,423 | |

**There are two ways to spend an `[any]`, and they are alternatives:**

- **Unroll it** — turn it into concrete accessors up front. Cost: a factorial premise population
  (`Σ N!/(N−k)!`). Benefit: the facts are concrete, so `delta` walks concrete paths and the graft
  stays cheap — 2.72 attachment points, 25 nodes per call.
- **Keep it** — leave the `[any]` in the fact and let each read synthesise through it. Cost: every
  read is a fixed point that makes no progress, the `[any]` never dies (98.5% of grafts hand it
  straight through), conclusions stay abstract so the graft attaches at 16.47 points, and every
  application costs 4× more.

The budget switches from the first mode to the second. That is the whole reason it cannot win, and it
is the same fact reported three ways across these documents: `concat`'s node total is invariant
(131.6 / 138.4 / 136.0 M) while the operation the budget governs goes to zero.

---

## 4. What this corrects, and what it does not

**Corrects.** An earlier note ([[any-read-fixed-point-mechanism]]) put this fixed point at the centre
of the conductor explosion, via `filterStartsWith`. On the fact side the round trip is measurably
*not* the default driver — 2 events — though it is precisely the right description of what happens
once the unroll stops. Both statements can hold because they describe different regimes; the note did
not say which regime it was measuring.

**Does not establish.**
- **`depthGainPerCall` is not a link count.** It reads 12.90 (off) and 21.03 (`L=0`), but `maxDepth`
  adds `ANY_ACCESSOR_DEPTH_CHARGE = 10` per `[any]`-owning node, so a result that gains an `[any]`
  gains ≥10 before any structural growth. The structural part is roughly 3 and 11, not 13 and 21.
- **Why only 40% of `L=0` remainders keep the `[any]`** where the minimal shape keeps it 100% of the
  time. At scale the `[any]` sits deep in a large tree and the read returns a subtree, not the whole
  fact; the "consumes nothing" extreme is 3% of those calls. The distribution between the two was
  not characterised.
- Whether 2 is stable. It is a single run, and a count that small could plausibly be 0 or 20 in
  another; the claim that survives either way is that it is negligible against 11.4 M.

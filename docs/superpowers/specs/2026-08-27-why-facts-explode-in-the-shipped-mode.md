# Why facts explode with TIFA-no-unroll + literal `[any]` matching

The shipped mode made the premise side small and flat. The fact side got worse. This is the
mechanism, measured on the conductor scoped arm (one entry point, one rule, frontier flags, 8 GB),
with the same jar for both columns.

---

## 1. The one-line answer

> **The premise reduction and the fact inflation are the same event.** TIFA emits `p.[any]` where it
> used to emit `p.a`, `p.b`, `p.c` … — so structure that used to be split across many concrete
> premise slots now merges into one. Fewer keys, therefore bigger values. And because `delta` strips
> only the short premise prefix, summary application then transplants **nearly the whole caller fact**
> into the callee's summary shape, and the result is `[any]`-terminated so the next call does it again.

---

## 2. Who manufactures the mass: summary application, 84.5% of it

`edgeStore --- by producer ---`, literal arm:

| producer | calls | growths | propagated mass | share |
|---|---:|---:|---:|---:|
| **SUMMARY** | 1,914,369 (66.7%) | **384,405** | **374,707,654** | **84.5%** |
| CALL | 542,303 (18.9%) | 106,097 | 51,136,013 | 11.5% |
| SEQUENT | 289,309 (10.1%) | 15,226 | 17,331,327 | 3.9% |
| TIFA_SEED | 33,822 | 0 | 76,044 | 0.02% |
| START | 35,102 | 155 | 775 | 0.00% |

`TIFA_SEED` — the initial-fact abstraction, the thing that stopped unrolling — contributes **0
growths and 0.02% of propagated mass**. It is not where the facts are. Summary application is, and
two thirds of its 1.9 M calls are no-ops that still pay for a merge.

---

## 3. What a summary application actually does

There is exactly **one graft call site in the shipped engine**,
`MethodCallSummaryHandler.kt:111-117`:

```kotlin
val mappedSummaryFacts = mapMethodExitToReturnFlowFact(summaryEdge.final)
... mappedSummaryFact.concat(factTypeChecker, summaryEffect.delta)
```

and the orientation is the opposite of the intuitive one:

- **receiver** = the *callee's* summary final fact — small, 18.5 nodes on average;
- **delta** = the *caller's own stored fact minus the premise prefix* — large, **71.8 nodes** on
  average, and it is grafted onto **every `isAbstract` node of the receiver**
  (`AccessTree.kt:2654`, `if (isAbstract && other != null)`), counted per traversal path with no
  result memo.

The biggest single event of the run says it in one line:

```
[C-concat +8005] graft delta(size=8006) onto receiver(size=1) -> 8006
  delta = <static>(__spring_registry__)...ExecutionDAO.conductorProperties.stack.buffer.Element.[any]/*
          ...buffer.Element.MapKey.[any]/*   ...buffer.Element.Element.[any]/*
          ...buffer.entries.Element.[any]/*  ...
```

**A callee whose entire summary is `*` — "returns its input taint unchanged" — causes the caller's
whole 8,006-path fact to be re-materialised at the return site.**

---

## 4. Head to head: the same jar, both modes

`-Dopentaint.apOpDiag=true`.

| | **literal (shipped)** | denotational | ratio |
|---|---:|---:|---:|
| `concat` calls | 1,090,728 | 4,985,471 | 0.22x |
| receiver (callee summary) nodes / call | 18.5 | 5.4 | 3.4x |
| receiver **abstract** nodes / call | 2.12 | 1.46 | 1.45x |
| **delta (caller fact ⧵ premise) nodes / call** | **71.8** | 24.7 | **2.9x** |
| **graft points / call** | **9.29** | 2.26 | **4.1x** |
| most graft points in one call | **1,291** | 63 | **20x** |
| growth / call | **90.2** | 25.8 | 3.5x |
| concats grafting an `[any]`-carrying delta | **59.1%** | 0.2% | 295x |
| … of which the result keeps the `[any]` | **98.8%** | 85% | |
| depth gain per concat | 21.0 | 16.7 | |
| **total nodes manufactured** | **98.4 M** | 128.7 M | **0.76x** |

**Read the last row before any of the others.** Literal matching manufactures *fewer* nodes overall.
It concentrates them: 4.6x fewer operations, each producing 3.5x more, into 4.4x fewer store slots.
That is why `propagatedPerGrowth` goes 50 → 333 while total store mass actually *falls* — the engine
is not making more structure, it is making the same structure in units too big to move.

---

## 5. The five things that let one application ship 72 nodes

### 5.1 `delta` no longer removes much of the fact

The premise is short, so stripping it leaves almost everything:

```
E-delta concretePremise calls=2,164,795 factNodes=251,470,580 remainderNodes=112,871,812
                        remainderPerFact=0.45  notSmaller=1,101,110      (50.9%)
E-delta anyPremise      calls=204,022   remainderNodes=456  remainderPerFact=0.00  notSmaller=0
```

Two things here. First, **an `[any]` premise leaves no remainder at all** (456 nodes across 204 k
calls) — that half works exactly as designed. The traffic is the *concrete* premises R2 emits over
the fact's own literal edges, 2.16 M calls, and there the remainder is 45% of the fact.

Second, **51% of those deltas are not smaller than the fact they came from.** The reason is in
`deltaImpl` (`AccessTree.kt:262-290`): when the matched node is abstract, the delta is
`removeAbstraction()`, which clears the abstraction **at the root only** — every interior and leaf
abstraction below it survives. So consuming a premise link can leave a delta the same size as the
fact.

### 5.2 A node under an `[any]` is a graft point, and the `[any]` edge is not filtered

`[any] -> *`: the node *below* the edge is abstract, hence a graft point. And the descent
(`AccessTree.kt:2678-2683`) only filters through **field** accessors —

```kotlin
val filteredOther = if (accessor.isFieldAccessor()) other?.limitFieldAccess(accessor, nestedAccessors)
                    else other
```

— so the delta passes an `[any]` edge **completely unfiltered**. A fact carrying `[any] -> *` at
nearly every node therefore has a graft point one step below nearly every node. Measured on the
conductor fact: d7 100 of 102 nodes own an `[any]`, d10 107 of 109.

### 5.3 The type filter switches itself off exactly where the mass is

```
I-filterTypes calls=10,131,574 hitRate=86.10% nodesPerMiss=58.66
I-filter emptyPath=758,323 anyTail=6,825 typed=9,366,426
        deltaNodes empty/anyTail/typed = 72,664,188 / 13,650 / 45,214,837
```

`JIRFactTypeChecker.accessorActualType` reads only the path's last step and returns `null` — i.e.
*accept everything* — for an empty path and for `AnyAccessor`, marks, `FinalAccessor`, statics and
type-info. **758 k graft points with an empty path carry 72.7 M delta nodes — 62% of all delta mass
is offered at a position where the type filter is disabled by construction**, against 45.2 M at the
9.4 M typed positions.

### 5.4 The graft bypasses the only contracting operator, and that operator refuses this shape anyway

`concat` rebuilds the receiver's spine through `bulkMergeAddAccessors` into a **fresh node with
`accessors == null`**, and `mergeAccessors` short-circuits that case by copying the other side
verbatim with a no-op `onOtherNode` (`AccessTree.kt:2886-2892`). So the `[any]`-suffix trim never
sees the newly written edges.

And where it does run, `AccessTreeAnySuffixMatcher` **cancels `isFinal` but deliberately not
`isAbstract`** — so `[any].*` does not subsume a sibling `f.*` whose node is abstract, even though it
denotes a superset. Its own source comment names the consequence: *"Abstract nodes are exactly the
graft points, and graft points per concat call is the quantity that runs away on conductor
(15.7 → 109.1 between the early and late windows)."* That 7x within one run is the self-amplification,
measured.

### 5.5 The result is `[any]`-terminated, so the next lap repeats

```
F-roundtrip concatAnyDelta=644,512  resultKeepsAny=636,942  depthGainPerCall=21.00
```

59% of concats graft an `[any]`-carrying delta and **98.8% of the results keep the `[any]`**. The new
leaves are abstract and `[any]`-terminated — i.e. they are graft points for the next summary
application. Nothing in the engine stops a freshly grafted abstract leaf from being grafted onto
again: `underGraft` exists but gates only a diagnostic counter.

`depthGainPerCall = 21` is two `[any]` levels at `ANY_ACCESSOR_DEPTH_CHARGE = 10` per application,
which is what drives the depth gate from 3 to 76 over 9,264 raises — and once it has ratcheted,
`stillParked = 0`: the only live bound has stopped bounding.

---

## 6. And then the store multiplies it again

The per-statement store holds ONE MERGED TREE per (premise, statement) and `add` returns **the whole
tree** on any change. The `bigFact` hall of fame catches one slot at four successive growths:

```
#1 paths=17612 nodes=827   #2 17604/823   #3 17602/823   #4 17599/823
```

Each growth added about three paths and re-shipped about seventeen thousand six hundred. Hence
`propagatedPerGrowth = 333` against the denotational arm's 50, and 443 M propagated against 199 M.

Concentration, not creation: **94.4% of all concat result mass sits on just two base kinds**
(`LocalVar` 53.4%, `<static>` 41.0%) and **69% on three methods** (`WorkflowExecutorOps#decide` 35.2%,
`#rerunWF` 24.9%, `#scheduleTask` 9.3%).

---

## 7. What would actually bite

Ranked by the measurement above, not by elegance.

1. **Return a delta from the store, not the merged tree.** 333 nodes shipped per growth that added 3
   is the largest single multiplier in the run, and nothing tried so far has touched it.
2. **Give the graft a result memo.** 79.2% of graft points re-offer the delta to a node already
   grafted in the same call; 59.5% sit strictly below another graft point. Both are already counted
   and neither is exploited.
3. **Make the type filter non-vacuous at `[any]` and empty-path positions**, which is where 62% of
   delta mass is offered with no test at all. (Cutting those steps outright converges the run *and*
   loses every finding — so this is "widen the filter", not "reject more".)
4. **Bound breadth.** `accessorCount()` is compared against no threshold anywhere.
5. **Re-price the depth gate** (`charge 1`, `ceiling 9`) — still the only lever measured to converge
   conductor *with* its findings, and the only one that is a cost-function fix rather than a
   coarsening.

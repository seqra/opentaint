# Why the fact grows after `concat`: the summary does not summarise

Third in the series, after `2026-08-25-any-unroll-growth-mechanics.md` (which measured that
`concatToLeafAbstractNodes` creates 131–151 M nodes, 98% of all nodes created) and
`2026-08-25-why-the-budget-does-not-help.md` (which showed that number is invariant under the
`[any]` budget). This one measures what a single graft does and why the result is ~5× its input.

**The answer in one line:** `concat` receives the callee's *conclusion* (6.3 nodes) and the caller's
*remainder below the matched premise* (23.6 nodes — **53% of the caller's whole fact**), and returns
conclusion + remainder. The call boundary does not shrink the fact; it re-roots most of it under a
new prefix. Then that happens 6,025,365 times.

---

## 1. What the two inputs are

`MethodCallSummaryHandler.kt:116`:

```kotlin
val summaryFactAp = mappedSummaryFact.concat(factTypeChecker, summaryEffect.delta)
```

- **receiver** = `mappedSummaryFact`, the callee's summary **conclusion** mapped back into the caller.
- **delta** = `summaryEffect.delta`, built at `MethodSummaryEdgeApplicationUtils.kt:23` as
  `methodInitialFactAp.delta(methodSummaryInitialFactAp)` — the caller's fact **minus the summary's
  premise prefix**, i.e. everything hanging below the part the premise matched.

So a summary application means: *the premise consumed this much of your fact; here is the conclusion;
re-attach the rest.* The size of the result is set by "the rest".

## 2. The rest is half the fact

New counters on `AccessTree.delta`, unbudgeted arm:

| | |
|---|---:|
| `delta()` calls | 11,437,909 |
| caller fact nodes fed in | 373,011,267 |
| remainder nodes handed to `concat` | 197,446,854 |
| **remainder / fact** | **0.53** |
| premise links, mean | **1.35** |
| calls whose remainder is no smaller than the fact | 5,240,909 (46%) |

Premises average **1.35 links** against facts that are 13–17 links deep. A premise that consumes one
link off a fifteen-link fact leaves fourteen links of remainder, and that remainder is what gets
copied. This is the whole mechanism: **summaries are keyed on short prefixes, facts are deep, so the
summary explains almost nothing about the fact and the fact survives the call intact.**

## 3. What one graft does

Deep profile, sampled 1 call in 512 (n = 11,768), unbudgeted arm — per call:

| | size (multiplicity) | distinct | abstract |
|---|---:|---:|---:|
| receiver (the conclusion) | 6.3 | 3.9 | 1.45 |
| delta (the caller's remainder) | 23.6 | 11.0 | |
| **result** | **30.5** | **14.2** | |

**Result / receiver = 4.8×.** And the growth is real, not a `size` artifact: **10.32 genuinely new
distinct nodes per call**, against a delta of 11.0 distinct. The ratio 10.32 / 11.0 = **0.94** says
the delta is copied *once* structurally and shared across the attachment points — interning is
working. Multiplied out: 6.0 M calls × 10.32 ≈ **62 M distinct nodes allocated by this one operation**.

The attachment count is measured exactly, not sampled:

| | unbudgeted |
|---|---:|
| graft points (abstract nodes the delta was offered to) | 16,385,846 |
| **points per call** | **2.72** |
| max points in one call | 247 |
| calls attaching at exactly 1 point | **4,728,375 (78%)** |
| calls attaching at ≥23 points | 104,248 (1.7%) |

**78% of grafts attach at exactly one point.** So the normal case is not multiplication — it is
*relocation*: take the caller's remainder, hang it under the conclusion, once.

Note 2.72 points/call against 1.45 abstract *distinct* nodes: `concatToLeafAbstractNodes` recurses
through `forEachAccessor` with no memo, so a node reachable by *m* paths is visited *m* times. **The
graft's cost is path-counted over a DAG**, which is why `AccessNode.size` (multiplicity) is the
correct cost unit for it, and why the 93× sharing inflation seen in the tree dumps is a cost fact and
not just bookkeeping.

## 4. Where the 151 M actually comes from

Growth per call, by log2 bucket, with each bucket's share of all nodes created:

| growth per call | calls | ~nodes | share |
|---|---:|---:|---:|
| 0–1 | 619,204 | 0.6 M | 0.4% |
| 2–3 | 434,601 | 1.3 M | 0.8% |
| 4–7 | 1,507,125 | 9.0 M | 5.4% |
| 8–15 | 980,565 | 11.8 M | 7.0% |
| **16–31** | **1,076,696** | **25.8 M** | **15.5%** |
| **32–63** | **809,569** | **38.9 M** | **23.3%** |
| **64–127** | **433,247** | **41.6 M** | **24.9%** |
| **128–255** | **138,039** | **26.5 M** | **15.9%** |
| 256–511 | 23,412 | 9.0 M | 5.4% |
| 512–1023 | 2,654 | 2.0 M | 1.2% |
| 1024–2047 | 253 | 0.4 M | 0.2% |

**Buckets 16–255 hold 79.6% of everything, spread over 2.46 M calls.** There is no dominating event:
the largest single graft in the whole run is +1,846 nodes and contributes 0.001%. This is a broad
middle, and the only way to move it is to move the *number of calls* or the *size of the remainder*.

For scale, the largest single graft:

```
[C-concat +1846] graft delta(size=345) onto receiver(size=22) -> 1868
    delta=.Element.Value.type.<get-default>.task/* .Element.Value.name.<get-default>.task/*
          .Element.Value.subWorkflowParam.name.<get-default>.task/* …
```

## 5. What coarsening does to it — and the guess it refutes

The natural guess is that an `[any]`-carrying premise consumes nothing (its read is a fixed point), so
it would leave the whole fact as the remainder and make the delta enormous. **That is wrong, and the
counters say so.** At `L=0`, where every unroll is refused and premises coarsen to `[any]`:

| | concrete premise | `[any]` premise |
|---|---:|---:|
| `delta()` calls | 2,356,858 | 257,155 |
| caller fact nodes | 347,467,333 | 27,611,793 |
| **remainder nodes** | 118,098,871 | **462** |
| **remainder / fact** | 0.34 | **0.00** |

An `[any]` premise produces an essentially **empty** delta — it takes the `SummaryExclusionRefinement`
path and grafts nothing at all. Coarsening does not enlarge the delta.

What it does instead is make the *conclusions* more abstract, which multiplies the attachment points:

| | unbudgeted | `L=0` |
|---|---:|---:|
| receiver abstract nodes (distinct, sampled) | 1.45 | 2.32 |
| **graft points per call** | **2.72** | **16.51** |
| max points in one call | 247 | **2,380** |
| calls attaching at ≥23 points | 1.7% | **13%** |
| distinct nodes created per call | 10.32 | **29.74** |
| distinct created / delta distinct | **0.94** (shared) | **1.67** (multiplied) |
| growth per call | 25.03 | **89.51** |
| share of nodes from calls growing ≥256 | 6.8% | **70.7%** |

Two things change together. The delta stops being shared — 1.67 distinct nodes created per distinct
delta node means the same delta is materialised differently at different points instead of once — and
the distribution flips from a broad middle to a heavy tail, with 8% of calls producing 71% of the
nodes. That is the mechanical content of "absorption is not cheaper".

## 6. The pattern

1. A summary is keyed on a **short premise** (1.35 links) because premises are what the abstraction
   emits, and it emits the shortest thing that answers a demand.
2. Facts are **deep** (13–17 links), because the `[any]` unroll built them that way
   ([[any-unroll-copies-the-carrier]]).
3. `delta()` therefore returns **53% of the fact** as remainder.
4. `concat` attaches that remainder under the conclusion — 78% of the time at exactly one point. The
   fact is **re-rooted, not reduced**: it crosses the call boundary at ~5× the conclusion's size and
   essentially its original information content.
5. The result is a caller fact at the next call site, where step 3 repeats.
6. 6,025,365 applications × ~10 new distinct nodes = ~62 M distinct nodes, 151 M by multiplicity.

**The lever this points at is not the graft.** It is either the premise length — a summary keyed on a
prefix long enough to consume the fact would return a small remainder — or the number of summary
applications. The `[any]` budget touches neither, which is why §5 of the budget document found the
131 M invariant.

## 7. What is not established

- **Whether longer premises are affordable.** "Consume more of the fact" means more distinct
  premises, i.e. exactly the population the earlier documents show exploding. This is the same
  dichotomy again and it is not resolved by anything here.
- **Why `remainderPerFact` is 0.53 rather than higher or lower.** 46% of `delta()` calls return a
  remainder no smaller than the fact, and mean premise length is 1.35, so a large share of calls are
  near-zero-length premises where the remainder *is* the fact. The distribution of remainder ratio by
  premise length was not measured.
- **Whether the 62 M distinct figure is live or garbage.** It is allocation, not residency; the
  interner and soft references decide what survives.
- Single samples per arm.

# The manager does stop the unroll. The work does not go away.

Answers a direct question about `2026-08-25-any-unroll-growth-mechanics.md`: if the unroll is doing
that, why doesn't the `[any]` manager's budget stop it?

**Short answer, in three parts.**

1. **It was switched off in every run in that document.** `opentaint.anyUnrollLimit` defaults to `-1`
   and `run2.sh` never set it. The 20,782 materialisations were measured with no budget at all. That
   is my omission and it should have been stated in the document.
2. **Switched on, it does precisely what the design says.** At `L=100` the pots fill to exactly 100,
   the worst pot refuses 45,281 reads, TIFA records 57 budget refusals, the unroll drops **62×**, the
   ladder shortens from depth 7 to depth 5, and the coarse `[any]` premise is emitted in place of the
   concrete ones. Nothing about the mechanism is broken.
3. **It does not help.** Both budgeted arms are *worse* than the unbudgeted one, and the operation
   budget says exactly why: the nodes were never in the unroll.

---

## The three arms

One Spring handler, one rule, same jar (`apop2-03209e38d2b77176`), `-Xmx8g`, IFDS budget 300 s.

| | manager off (`-1`) | `L=100` | `L=0` |
|---|---:|---:|---:|
| exit | 253 (low memory) | **254 (timeout)** | **254 (timeout)** |
| wall | **209 s** | 280 s | 309 s |
| IFDS progress | **2,106,997** (4 left) | 872,107 (2 left) | **770,226** (3 left) |
| findings | 2 | 2 | 2 |

Findings are identical in all three. At this scope the cut is **lossless and useless** at the same
time — which is a sharper form of the old dichotomy, not an instance of it.

## The manager itself, at `L=100`

```
mints=159  mintsBySite=prepend:155,rawEdge:4  unions=147  dagFusions=18  transitions=429
reads=182371  reusedFree=119854  refused=62088  absorptions=51646
maxPotTotal=100  maxPotRefusals=45281
TIFA: unrollRequests=175  accessorsOffered=511  materialised=333  refusedByBudget=57
```

`maxPotTotal=100` is the limit, exactly. The budget fills, refuses, and hands over to the coarse
premise. Compare the unroll against the unbudgeted arm:

| | off | `L=100` | ratio |
|---|---:|---:|---:|
| unroll requests | 4,076 | 175 | 23× |
| accessors offered | 79,142 | 511 | 155× |
| **materialised** | 20,782 | **333** | **62×** |
| carrier nodes copied | 3,518,558 | 1,807 | 1,947× |
| **nodes the unroll added to `added`** | **2,681,364** | **1,397** | **1,920×** |
| deepest prefix reached | 7 | 5 | |
| premises emitted | 333,881 | 88,804 | 3.8× |

The generator is essentially switched off. And the analysis gets slower.

## Why: the mass was never in the unroll

The operation budget across the three arms — same counters as the mechanics document:

| | off | `L=100` | `L=0` |
|---|---:|---:|---:|
| **A** `unrollAnyAccessors` → nodes into `added` | 2,681,364 | 1,397 | **0** |
| **B** `getChild` `[any]` synthesis — calls | 58,765 | 202,316 | **27,883,524** |
| **B** nodes created | 176,295 | 293,289 | **41,850,681** |
| **C** `concat` — calls | 5,199,708 | 1,814,122 | 1,337,884 |
| **C** nodes per call | 25.31 | **76.30** | **101.67** |
| **C** nodes created | **131,623,220** | **138,410,824** | **136,023,638** |
| **D** `filterStartsWith` — nodes in | 70,712,505 | 111,834,159 | — |

Read the C row across. **A falls from 2.68 M to 0. C stays at 131.6 M → 138.4 M → 136.0 M.** The
node mass is conserved to within 5% while the operation the budget governs goes to zero. A was never
more than **2%** of the nodes created.

Two mechanisms move the work rather than removing it:

**The `[any]` stops being consumed.** The unroll is what *spends* an `[any]`: it turns
`R.[any]` into a concrete `R.c`, and the `[any]` is one step shorter. Refuse it and the `[any]`
stays in the fact forever, so every subsequent read of a covered accessor is answered by `getChild`'s
synthesis arm instead. At `L=0` that is **27.9 million** synthesised reads against 58,765 with the
budget off — **475×** — over 1.07 *billion* literal nodes scanned.

**The premises get coarser, and the graft is superlinear in coarseness.**
`concatToLeafAbstractNodes` attaches the delta at *every abstract node* of the receiver. A summary
keyed on `X.[any]` matches more caller facts than one keyed on `X.a`, and its delta has more abstract
nodes to graft at. So each application does more: **25.31 → 76.30 → 101.67 nodes per call**, a 4×
worsening as the budget tightens. Fewer, bigger, more widely-matching grafts.

The IFDS step rate shows the same thing from outside: ~12,000 steps/s unbudgeted against ~3,100 at
`L=100`, a 4× slowdown per step even though the abstraction is doing 3.8× less emitting.

## What this changes

- **§4.2 of the manager results document stands but was under-scoped.** It reported
  `refusedByBudget=0` at `L=100` on whole-project conductor and concluded the manager "bounds a
  mechanism conductor barely uses". At single-endpoint scope the same limit gives
  `refusedByBudget=57` and 62,088 manager refusals — the budget's bite is scope-dependent, because
  the same limit is multiplied by however many origins the workload mints (155 here, 12,170 on
  thingsboard). The conclusion was right for the wrong reason: the manager is not weak, it is
  aimed at 2% of the nodes.
- **The lever is C, not A.** Anything that reduces the *premise population* feeds C coarser deltas
  and is liable to lose on net. What would actually reduce C is reducing the number of abstract
  nodes it grafts at, or the number of summary applications — neither of which the budget touches.
- **"Emit the coarse `[any]` premise instead" is not a saving.** It is a trade of many precise
  premises for one general one, and general premises are more expensive to apply in this engine.
  §5.3 of the design treats refusal as a pure coarsening with a precision cost; measured, it has a
  throughput cost that dominates.

## What is not established

- **Whether C's growth is the same nodes in each arm.** The totals match to 5%, but no counter
  attributes a grafted node to the premise family that produced it, so "conserved" is an aggregate
  statement, not an identity.
- **Why `L=0` mints 439 `rawEdge` origins against 4 at `L=100`.** A refused read returns null and
  some edge is then rebuilt raw. Small in absolute terms, unexplained.
- Single samples per arm; the three arms differ by far more than the ~5% run-to-run variation seen
  earlier on volume counters, but that variation was not re-measured here.

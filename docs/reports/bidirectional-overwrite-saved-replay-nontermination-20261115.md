# Ordinary overwrites restore a saved-replay demand cycle

15 November 2026. Synthetic data-flow reachability; FULL mark T only.
Counterexample to [prepared-child saved replay](../design/bidirectional-prepared-child-saved-replay-20261115.md)
with [non-empty MAY](../../spec/non-empty-may.md), bounded one-field refinement,
and same-lane uniform coverage. Production is unchanged. Follow
[proof-guide.md](../../spec/proof-guide.md).

The decisive change from the previous nested example is ordinary `g` writes
before and after the two branches. These are real writes, not cleaner rules.
They leave `{g}` on both NORMAL saved relations. The selected saved-replay
routing explicitly requires empty real exclusions, so it does not route the
parent uncertainty through prepared children in this case.

Latest finite reference: **run-61**. Lean checks the complete cold trace through
**run-13** and the arbitrary later recurrence separately. Native component tests:
**4 passed**. No project run or full native implementation of the proposal is
claimed. The proof has no hard iteration limit.

## Code and notation

[Compilable Java](../../spec/lean/proposals/overwrite-saved-replay-cycle-20261115/OverwriteReplay.java).
All transfer comes from ordinary analyzed instructions. `produce` has a call-site
mark-assignment rule at `ret.f.g` and below; `observe` has the observation condition
`CM(arg0.[any],T)`. No pass rule, cleaner, loop, recursion, static, intrinsic MAY
or unresolved transfer model is used. `produce` allocates a finite tree; allocation
adds no T by itself. The two rules run at their call sites in `entry`.

```java
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
Node wrapper(Node x, boolean down) { return choose(x, down); }
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce(); // assigns T at x.f.g and descendants
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);        // checks CM(w.[any],T)
}
```

`M = [any]`; `NE = [non-empty-may]`; `U = [any-taint]`.
`N/D` are NORMAL/DEMAND. `{g}` is a real suffix-scope exclusion.
All unlabelled field/mark exclusions and protection flags are empty/false.
A demand is shown as **entry selector -> paired exit selector**, in the current
run direction. Thus a backward demand starts at `ret`, not at argument `x`.
Forward summaries are below the declaration; backward summaries are above it.
Raw initials are identity edges. All listed initials have FLOW and NORMAL;
normalization of their `$` to `*` occurs only at publication.

## Native transfer audit and closed return cone

The saved records, derived from the body (not predefined), are:

```text
Wg: x.*       -> ret.f.f.* {g}, N
Rg: x.f.f.*   -> ret.*     {g}, N
```

The two producer directions contribute these shapes. Reversal puts
shared `{g}` on the result of the opposite record, with an empty premise
exclusion. The pre-write affects Wg and the post-write affects Rg. Wg is learned forward;
Rg is learned backward. Their producer directions remain distinct.

```text
owned raw x.f.*/FLOW,N
  + opposite Rg
  = ret.M/FLOW,D                 // unknown second f, not a real field cut
  + paired exit ret.f.*/FLOW
  = ret.f.M/FLOW,D
```

The MAY result has no real exclusion. The next handoff forgets demand field
exclusions as specified. The concrete T input `x.f.g.U/T,N` cannot use Rg,
since `g != f`; Wg instead produces `ret.f.f.f.g.U/T,N` with no exclusion.
Thus the uncertainty is conditional query work, not another real marked path.

`OverwriteSavedReplayCycleComponentsTest` checks raw EXACT/STAR writes,
NORMAL normalization, opposite reader application, reversal, and real uniform
input application against native operators. The NORMAL duplicate check uses the complete E-aware native image; the result
does not depend on republishing already saved NORMAL relations. The executable
Lean model extends the prior prefix reference with those real exclusions and strong overwrites.
It does not claim a whole-core simulation theorem.

The reference includes the complete argument-to-return cone. The argument-side
mutation result and fresh allocations cannot create an additional return
provider: the returned object is either `x.f.f`, or a fresh object whose only
input reference is at `f.f`. Any input-derived marked return therefore uses one
of Rg/Wg. The `g` writes may kill paths, but cannot add another return path.
Argument-side aliases use a different conclusion base and do not subsume these
return rows. No extra alias-derived return transfer is assumed. This scope
boundary is part of the counterexample, not a new analyzer transfer rule.

## Cold iteration trace

Each run is drained before handoff. `choose` may receive saved-replay offers
when its current demand is empty; that correctly produces no new initials.
The table counts qualified demand rows, not just executable MAY union rows.

| Run | Direction | Field limit | wrapper outgoing demand | choose outgoing demand |
|---:|---|---:|---:|---:|

| 1 | forward | 1 | 1 | 2 |
| 2 | backward | 1 | 2 | 3 |
| 3 | forward | 2 | 4 | 6 |
| 4 | backward | 3 | 7 | 4 |
| 5 | forward | 4 | 12 | 0 |
| 6 | backward | 5 | 6 | 0 |
| 7 | forward | 6 | 4 | 0 |
| 8 | backward | 7 | 4 | 0 |
| 9 | forward | 8 | 4 | 0 |
| 10 | backward | 9 | 4 | 0 |
| 11 | forward | 10 | 4 | 0 |
| 12 | backward | 11 | 4 | 0 |
| 13 | forward | 12 | 4 | 0 |

### Run-1: forward, limit 1

```java
// Demand:
//   {}
// Submitted:
//   x.M/T,D
//   x.f.NE/T,D
// Emitted raw identity initials:
//   x.*/FLOW -> x.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.*/T,N
// Emitted raw identity initials:
//   x.*/FLOW -> x.*/FLOW,N
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
```

```java
// Entry: unrestricted ZERO seed.
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.NE/T,D
//   1: y.M/T,D
//   2: z.M/T,D
//   3: w.M/T,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
```


### Run-2: backward, limit 1

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.f.NE/FLOW,D
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.f.NE/FLOW -> x.*/FLOW
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
```

```java
// Published current control: ZERO -> DemandTarget,D.
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: observation -> wrapper(z) -> wrapper(y) -> wrapper(x) -> producer.
// Final packet overlaps producer position x.f.g.U/T; its GEN yields DemandTarget.
// Call-boundary packets (in traversal order):
//   0: w.M/T,D
//   1: z.M/T,D
//   2: y.M/T,D
//   3: x.M/T,D
```


### Run-3: forward, limit 2

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.f.NE/FLOW -> ret.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.g.*/FLOW -> ret.M/FLOW,D
```

```java
// Demand:
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.NE/FLOW -> ret.*/FLOW
//   x.f.NE/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.*/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   x.*/FLOW -> ret.f.f.*/FLOW {g},N
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
```

```java
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.g.U/T,N
//   1: y.M/T,D
//   2: z.M/T,D
//   3: w.M/T,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
```


### Run-4: backward, limit 3

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.M/FLOW,D
//   ret.*/FLOW -> x.f.NE/FLOW,D
//   ret.*/FLOW -> x.f.g.M/FLOW,D
//   ret.*/FLOW -> x.f.f.*/FLOW {g},N
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.M/FLOW -> x.f.g.*/FLOW
//   ret.f.NE/FLOW -> x.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.f.f.*/FLOW {g},N
//   ret.f.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.f.g.M/FLOW,D
//   ret.f.*/FLOW -> x.f.f.NE/FLOW,D
//   ret.f.f.*/FLOW -> x.f.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Demand:
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.f.g.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.g.*/FLOW
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published current control: ZERO -> DemandTarget,D.
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: observation -> wrapper(z) -> wrapper(y) -> wrapper(x) -> producer.
// Final packet overlaps producer position x.f.g.U/T; its GEN yields DemandTarget.
// Call-boundary packets (in traversal order):
//   0: w.M/T,D
//   1: z.M/T,D
//   2: y.M/T,D
//   3: x.M/T,D
```


### Run-5: forward, limit 4

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
//   x.f.NE/FLOW -> ret.*/FLOW
//   x.f.NE/FLOW -> ret.f.*/FLOW
//   x.f.g.M/FLOW -> ret.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.$/FLOW -> x.f.g.$/FLOW,N
//   x.f.g.U/FLOW -> x.f.g.U/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.M/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
//   x.*/FLOW -> ret.f.f.*/FLOW {g},N
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.g.U/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.f.*/FLOW -> ret.f.f.NE/FLOW,D
```

```java
// Demand:
//   x.f.M/FLOW -> ret.f.*/FLOW
//   x.f.g.M/FLOW -> ret.f.*/FLOW
//   x.f.f.NE/FLOW -> ret.f.*/FLOW
//   x.f.f.NE/FLOW -> ret.f.f.*/FLOW
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.$/T,N
//   x.f.g.U/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
// Emitted raw identity initials:
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.$/FLOW -> x.f.g.$/FLOW,N
//   x.f.g.U/FLOW -> x.f.g.U/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   {}
```

```java
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.g.U/T,N
//   1: y.M/T,D; y.f.f.f.g.U/T,N
//   2: z.M/T,D; z.f.g.U/T,N
//   3: w.M/T,D; w.f.f.f.g.U/T,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
// NORMAL witnesses also give the retained ZERO -> NormalTarget(id),N.
// Existing identical NORMAL Target publication is skipped.
```


### Run-6: backward, limit 5

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.f.g.M/FLOW,D
//   ret.f.*/FLOW -> x.f.f.M/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.*/FLOW
//   ret.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.NE/FLOW -> x.f.g.U/FLOW
//   ret.f.NE/FLOW -> x.f.g.*/FLOW
//   ret.f.NE/FLOW -> x.f.f.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.g.*/FLOW
//   ret.f.f.NE/FLOW -> x.f.f.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Demand:
//   {}
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
//   ret.f.f.$/T,N
//   ret.f.f.*/T,N
// Emitted raw identity initials:
//   {}
```

```java
// Published current control: ZERO -> DemandTarget,D.
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: observation -> wrapper(z) -> wrapper(y) -> wrapper(x) -> producer.
// Final packet overlaps producer position x.f.g.U/T; its GEN yields DemandTarget.
// Call-boundary packets (in traversal order):
//   0: w.M/T,D
//   1: z.M/T,D
//   2: y.M/T,D
//   3: x.M/T,D
```


### Run-7: forward, limit 6

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
//   x.f.g.M/FLOW -> ret.f.*/FLOW
//   x.f.f.M/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
//   x.f.f.f.f.f.g.U/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.$/FLOW -> x.f.g.$/FLOW,N
//   x.f.g.U/FLOW -> x.f.g.U/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
//   x.f.f.f.*/FLOW -> x.f.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.$/T,N
//   x.f.g.U/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
//   x.f.f.f.*/T,N
// Emitted raw identity initials:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   {}
```

```java
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.g.U/T,N
//   1: y.M/T,D; y.f.f.f.g.U/T,N
//   2: z.M/T,D; z.f.g.U/T,N; z.f.f.f.f.f.g.U/T,N
//   3: w.M/T,D; w.f.f.f.g.U/T,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
// NORMAL witnesses also give the retained ZERO -> NormalTarget(id),N.
// Existing identical NORMAL Target publication is skipped.
```


### Run-8: backward, limit 7

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Demand:
//   {}
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
//   ret.f.f.$/T,N
//   ret.f.f.*/T,N
// Emitted raw identity initials:
//   {}
```

```java
// Published current control: ZERO -> DemandTarget,D.
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: observation -> wrapper(z) -> wrapper(y) -> wrapper(x) -> producer.
// Final packet overlaps producer position x.f.g.U/T; its GEN yields DemandTarget.
// Call-boundary packets (in traversal order):
//   0: w.M/T,D
//   1: z.M/T,D
//   2: y.M/T,D
//   3: x.M/T,D
```


### Run-9: forward, limit 8

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
//   x.f.f.f.f.f.g.U/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
// Emitted raw identity initials:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   {}
```

```java
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.g.U/T,N
//   1: y.M/T,D; y.f.f.f.g.U/T,N
//   2: z.M/T,D; z.f.g.U/T,N; z.f.f.f.f.f.g.U/T,N
//   3: w.M/T,D; w.f.f.f.g.U/T,N; w.f.f.f.f.f.f.f.g.U/T,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
// NORMAL witnesses also give the retained ZERO -> NormalTarget(id),N.
// Existing identical NORMAL Target publication is skipped.
```


### Run-10: backward, limit 9

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Demand:
//   {}
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
//   ret.f.f.$/T,N
//   ret.f.f.*/T,N
// Emitted raw identity initials:
//   {}
```

```java
// Published current control: ZERO -> DemandTarget,D.
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: observation -> wrapper(z) -> wrapper(y) -> wrapper(x) -> producer.
// Final packet overlaps producer position x.f.g.U/T; its GEN yields DemandTarget.
// Call-boundary packets (in traversal order):
//   0: w.M/T,D
//   1: z.M/T,D
//   2: y.M/T,D
//   3: x.M/T,D
```


### Run-11: forward, limit 10

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
//   x.f.f.f.f.f.g.U/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
// Emitted raw identity initials:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   {}
```

```java
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.g.U/T,N
//   1: y.M/T,D; y.f.f.f.g.U/T,N
//   2: z.M/T,D; z.f.g.U/T,N; z.f.f.f.f.f.g.U/T,N
//   3: w.M/T,D; w.f.f.f.g.U/T,N; w.f.f.f.f.f.f.f.g.U/T,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
// NORMAL witnesses also give the retained ZERO -> NormalTarget(id),N.
// Existing identical NORMAL Target publication is skipped.
```


### Run-12: backward, limit 11

```java
// Published summaries:
//   ret.*/FLOW -> x.M/FLOW,D
//   ret.*/FLOW -> x.f.M/FLOW,D
//   ret.f.*/FLOW -> x.M/FLOW,D
//   ret.f.*/FLOW -> x.f.M/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand:
//   ret.M/FLOW -> x.*/FLOW
//   ret.M/FLOW -> x.f.*/FLOW
//   ret.f.M/FLOW -> x.*/FLOW
//   ret.f.M/FLOW -> x.f.*/FLOW
// Submitted:
//   ret.M/T,D
// Emitted raw identity initials:
//   ret.$/FLOW -> ret.$/FLOW,N
//   ret.*/FLOW -> ret.*/FLOW,N
//   ret.f.$/FLOW -> ret.f.$/FLOW,N
//   ret.f.*/FLOW -> ret.f.*/FLOW,N
//   ret.f.f.$/FLOW -> ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW -> ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Demand:
//   {}
// Submitted:
//   ret.$/T,N
//   ret.*/T,N
//   ret.f.$/T,N
//   ret.f.*/T,N
//   ret.f.f.$/T,N
//   ret.f.f.*/T,N
// Emitted raw identity initials:
//   {}
```

```java
// Published current control: ZERO -> DemandTarget,D.
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: observation -> wrapper(z) -> wrapper(y) -> wrapper(x) -> producer.
// Final packet overlaps producer position x.f.g.U/T; its GEN yields DemandTarget.
// Call-boundary packets (in traversal order):
//   0: w.M/T,D
//   1: z.M/T,D
//   2: y.M/T,D
//   3: x.M/T,D
```


### Run-13: forward, limit 12

```java
// Demand:
//   x.M/FLOW -> ret.*/FLOW
//   x.M/FLOW -> ret.f.*/FLOW
//   x.f.M/FLOW -> ret.*/FLOW
//   x.f.M/FLOW -> ret.f.*/FLOW
// Submitted:
//   x.M/T,D
//   x.f.g.U/T,N
//   x.f.f.f.g.U/T,N
//   x.f.f.f.f.f.g.U/T,N
// Emitted raw identity initials:
//   x.$/FLOW -> x.$/FLOW,N
//   x.*/FLOW -> x.*/FLOW,N
//   x.f.$/FLOW -> x.f.$/FLOW,N
//   x.f.*/FLOW -> x.f.*/FLOW,N
//   x.f.g.*/FLOW -> x.f.g.*/FLOW,N
//   x.f.f.$/FLOW -> x.f.f.$/FLOW,N
//   x.f.f.*/FLOW -> x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.M/FLOW,D
//   x.*/FLOW -> ret.f.M/FLOW,D
//   x.f.*/FLOW -> ret.M/FLOW,D
//   x.f.*/FLOW -> ret.f.M/FLOW,D
```

```java
// Demand:
//   {}
// Submitted:
//   x.$/T,N
//   x.*/T,N
//   x.f.$/T,N
//   x.f.*/T,N
//   x.f.g.*/T,N
//   x.f.f.$/T,N
//   x.f.f.*/T,N
// Emitted raw identity initials:
//   {}
Node choose(Node x, boolean down) {
    x.g = new Node();
    Node y;
    if (down) y = x.f.f;
    else {
        Node t = new Node(); t.f = x;
        y = new Node(); y.f = t;
    }
    y.g = new Node();
    return y;
}
// Published summaries:
//   {}
```

```java
// Entry control demand: ZERO -> Target (paired selectors in the current direction).
// Submitted ZERO; emitted ZERO identity.
// Traversal: producer -> wrapper(x) -> wrapper(y) -> wrapper(z) -> observation.
// Call-boundary packets (in traversal order):
//   0: x.f.g.U/T,N
//   1: y.M/T,D; y.f.f.f.g.U/T,N
//   2: z.M/T,D; z.f.g.U/T,N; z.f.f.f.f.f.g.U/T,N
//   3: w.M/T,D; w.f.f.f.g.U/T,N; w.f.f.f.f.f.f.f.g.U/T,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
// Published current control: ZERO -> DemandTarget,D.
// NORMAL witnesses also give the retained ZERO -> NormalTarget(id),N.
// Existing identical NORMAL Target publication is skipped.
```

## Stationary recurrence after run-9

In each traversal frame, the wrapper retains exactly these four demand rows:

```text
M     -> *
f.M   -> *
M     -> f.*
f.M   -> f.*
```

These are paths below `x` forward, or below `ret` backward; they are not facts
whose base is the field `f`. All marks are FLOW. The same four MAY publications recur. Rg/Wg remain in the saved NORMAL
store; exclusion-aware precoverage avoids republishing them.
Both saved record provenance lanes persist. `choose` has no current DATA rows.

At any later forward field limit >= 8, let
`U_k = x.f^(2k+1).g.U/T,N`, and `M = x.M/T,D`.
The exact three-call closure is:

```text
x: {U_0}
y: {U_1, M}
z: {U_0, U_2, M}
w: {U_1, U_3, M}
```

All paths fit the limit: the longest has eight fields. Backward starts with
`w.M/T,D` and each of the three calls gives the same MAY need at its argument.
This need reaches the configured producer at `x.f.g`, and produces the fresh
root `ZERO -> DemandTarget,D`. Forward's `w.M/T,D` also creates that Target.
A retained NORMAL observation does not remove an anonymous demand Target.
Consequently root ZERO remains admitted on every next iteration.

Without NORMAL precoverage, relative C5 also renews a writer cut. The checked
reference uses the full E-aware NORMAL image to discard that duplicate work.
Even with that stronger precoverage, Rg repeatedly creates intrinsic root MAY
without any global field cut. Raising the global field limit cannot resolve
it. The exact and child probes are present; the result is not caused by omitting them or by ending a run before fixed point.

## Constructive proof and validation

The [proof package](../../spec/lean/proposals/overwrite-saved-replay-cycle-20261115/README.md)
contains the executable ordinary-overwrite extension, frozen complete cold
states, generic later C2/C5 packets, caller closure and ZERO/Target recurrence.
`OverwriteConcrete.lean` proves the two ordinary return transfers for every
concrete field word; its three theorems have no axiom dependencies.
Validation passed: **88 new theorems, 998 audited declarations, 64 modules**.
The full dependency rebuild passed; the extra concrete-word module was checked
against the same dependency hashes. Four native operator tests passed.

Python generates witnesses only. Lean checks them and an induction for all
later runs; no iteration cap is a premise. Only constructive foundation axioms
`propext` and `Quot.sound` are permitted.

The counterexample falsifies a universal termination claim for the selected
approach. It does not invalidate its supported empty-exclusion child-cover
proof or propose silently extending that scope. Extending the pruning to real
exclusions requires another complete child-cover and service proof.


# Synthetic nested-call demand cycle without loops or special rules

15 November 2026. A termination counterexample to the selected
[non-empty-MAY](../../spec/non-empty-may.md),
[bounded refinement](../design/bidirectional-bounded-demand-refinement-20261114.md)
and [same-lane uniform coverage/reply folding](../design/bidirectional-same-lane-uniform-termination-20261114.md)
proposal. Follow [proof-guide.md](../../spec/proof-guide.md).

**Result:** a wrapper around a two-branch ordinary method reaches a stationary,
nonempty refinement frontier. Each later forward/backward pair regenerates it.
This holds without an iteration limit. The reference capture reaches **run-31**;
the constructive induction, rather than that finite capture, proves recurrence.
Production is unchanged. This is a synthetic data-flow reachability example.

## 1. Scope and code

No program loops, call recursion, cleaner rules, pass rules, unresolved-library
MAY transfer, predefined DATA summaries, statics or alias expansion are used.
Use FULL marks with one nonprimitive full mark T. All compared memberships
are plain, with empty field/mark exclusions. Branches use the existing
path-insensitive union. Keep saved NORMAL replay unchanged, before current
callee-demand admission, as required by the selected call policy.

[Compilable ordinary code](../../spec/lean/proposals/nested-saved-replay-cycle-20261114/NestedReplay.java):

```java
final class Node { Node f; Node g; Node() {} }

Node produce() {
    Node x = new Node();
    x.f = new Node();
    x.f.g = new Node();
    return x;
}
void observe(Node x) {}

Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();
    Node y = wrapper(x, b1);
    Node z = wrapper(y, b2);
    Node w = wrapper(z, b3);
    observe(w);
}
```

Only two configured rules exist:

```text
At a produce() call:
    condition = true
    assign T at return.f.g and all its descendants
    // Ordinary FULL producer action: return.f.g.MUST/T, NORMAL if uncut.

At an observe(a) call:
    condition = ContainsMark(a.MAY, T)
    emit the ordinary observation Target with the witness layer
```

The method bodies and constructors are analyzed ordinary code. These rules
are call-site rules in `entry`; they do not supply custom summaries for
`choose` or `wrapper`. In particular, MAY is not a rule action here.

## 2. Notation and the projection

`$` = EXACT, `*` = STAR, `MAY` = `[any]`, `NE` = non-empty-MAY,
`MUST` = `[any-taint]`; N/D are NORMAL/DEMAND. `f != g`.
Demands are `[Dc ; Dp]`, not forward transfer arrows. All published relations
below have one premise. An emitted initial `A` starts as `A -> A` with its
listed layer. FLOW EXACT results normalize to STAR at summary storage.
The field-limit schedule is `1,1,2,3,...`.

The trace is the complete return-DATA and observation projection for the
three relevant owners: `entry`, `wrapper`, `choose`. Ordinary ZERO-to-ZERO
control and unchanged input identities are factored out, not deleted from
the analyzed program. They cannot replace a return-DATA relation: the output
base differs. Unused argument/local facts do not reach `observe(w)`.

The other fully analyzed bodies have the following common annotation in
every run:

```text
Node.<init>, produce, observe:
    DATA demand:          empty
    submitted DATA:       empty
    emitted DATA initials: empty
    published DATA:       empty
    ordinary ZERO control: ZERO -> ZERO, NORMAL
```

Their ZERO-only control can be replayed from the persisted NORMAL basis;
it creates no refinement demand. `produce` has no marked input: the
configured assignment is applied at its call in `entry`. `observe` has no
rule in its body: the configured check is applied at its call in `entry`.
Constructing unmarked nodes is not an intrinsic-MAY producer. Their
individual ZERO callbacks are irrelevant to the DATA/Target recurrence.

Only observation summaries are listed for `entry`. Its persisted NORMAL
ZERO-to-ZERO summary is unchanged. A NORMAL observation is first obtained
at run-5. Later identical `ZERO -> NormalTarget(id)` publication is skipped
under the existing persistence rule; anonymous DEMAND observations remain.

## 3. Where MAY is recreated

Ordinary code first derives these NORMAL records in both owners:

```text
Forward producer record W:   x.*   -> ret.f.f.*
Backward producer record:    ret.* -> x.f.f.*
Forward view of the latter R: x.f.f.* -> ret.*
```

`choose` derives W at run-3; both owners derive the backward record at
run-4; `wrapper` derives W at run-5. None is assumed at run-1.

Now examine a forward wrapper query created from the real marked input:

```text
Own demand:             x.MAY/FLOW
Real submitted input:   x.f.g.MUST/T, NORMAL
C2 starts:              x.f.*/FLOW, NORMAL
                        x.$/FLOW, NORMAL  // Existing conditional prefix probe.

wrapper passes x.f.*/FLOW to choose.
choose has no current demand from run-6 onward.
Saved NORMAL replay still runs:
    x.f.* + opposite-direction R(x.f.f.* -> ret.*)
        = ret.MAY/FLOW, DEMAND

wrapper publishes, after its own C5:
    x.f.*/FLOW -> ret.MAY/FLOW, DEMAND
```

The real `x.f.g.MUST/T` does **not** match R: its next field is g, not f.
The coarse STAR hypothesis has lost that distinction. The allowed
opposite-direction inside match recreates the uncertainty in the wrapper.
Saved replay happens even when `choose` has no current demand.

The one-field plan is included. For a root MAY demand it can prepare
`x.$`, `x.*`, `x.f.$`, `x.f.*`. The saved reader needs `x.f.f`:

```text
x.f.$ + R -> no result
x.f.* + R -> ret.MAY, DEMAND
```

Another split at f would require a two-field initial under that root
selector's one-field budget. A separate deeper row can have its own child
family; it cannot recursively increase the root row's budget or silently
change all sharing consumers' routing. No additional saved-replay pruning
is part of the selected proposal.

## 4. Per-run annotations

Forward: demand, offers and raw initials are above each declaration; publications are below it. Backward: publications are above, and demand, offers and initials are below. `ret` is the return position, not another local variable. All FLOW initials below are conditional NORMAL hypotheses; they do not assert an actual T at that position.

### Run-1: forward, limit 1

```java
// Demand:
//   none
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // x.f.NE/T,D
    Node y = wrapper(x,b1); // y.MAY/T,D
    Node z = wrapper(y,b2); // z.MAY/T,D
    Node w = wrapper(z,b3); // w.MAY/T,D
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.MAY/T,D
//   x.f.NE/T,D
// Emitted initials:
//   x.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.MAY/FLOW,D
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.*/FLOW,N
// Emitted initials:
//   x.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published summaries:
//   x.*/FLOW -> ret.MAY/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
```

### Run-2: backward, limit 1

```java
// Published observation summary:
//   ZERO -> DemandTarget,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // Backward x: x.MAY/T,D
                            // Producer overlap at x.f.g renews permission.
    Node y = wrapper(x,b1); // Backward y: y.MAY/T,D
    Node z = wrapper(y,b2); // Backward z: z.MAY/T,D
    Node w = wrapper(z,b3); // Backward w: w.MAY/T,D
    observe(w);            // Target-guided ZERO starts the ordinary MAY/T check.
}
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.MAY/FLOW,D
//   ret.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
// Submitted:
//   ret.MAY/T,D
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.f.NE/FLOW,D
//   ret.f.*/FLOW -> x.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
//   [ret.f.NE/FLOW ; x.*/FLOW]
// Submitted:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
```

### Run-3: forward, limit 2

```java
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // x.f.g.MUST/T,N
    Node y = wrapper(x,b1); // y.MAY/T,D
    Node z = wrapper(y,b2); // z.MAY/T,D
    Node w = wrapper(z,b3); // w.MAY/T,D
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
```

```java
// Demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.*/FLOW]
//   [x.f.NE/FLOW ; ret.*/FLOW]
// Submitted:
//   x.MAY/T,D
//   x.f.g.MUST/T,N
// Emitted initials:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.MAY/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.MAY/FLOW,D
//   x.f.g.*/FLOW -> ret.MAY/FLOW,D
```

```java
// Demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.NE/FLOW ; ret.*/FLOW]
//   [x.f.NE/FLOW ; ret.f.*/FLOW]
// Submitted:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.*/FLOW,N
// Emitted initials:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published summaries:
//   x.*/FLOW -> ret.f.f.*/FLOW,N
//   x.f.*/FLOW -> ret.MAY/FLOW,D
//   x.f.*/FLOW -> ret.f.MAY/FLOW,D
//   x.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
```

### Run-4: backward, limit 3

```java
// Published observation summary:
//   ZERO -> DemandTarget,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // Backward x: x.MAY/T,D
                            // Producer overlap at x.f.g renews permission.
    Node y = wrapper(x,b1); // Backward y: y.MAY/T,D
    Node z = wrapper(y,b2); // Backward z: z.MAY/T,D
    Node w = wrapper(z,b3); // Backward w: w.MAY/T,D
    observe(w);            // Target-guided ZERO starts the ordinary MAY/T check.
}
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.MAY/FLOW,D
//   ret.*/FLOW -> x.f.MAY/FLOW,D
//   ret.*/FLOW -> x.f.NE/FLOW,D
//   ret.*/FLOW -> x.f.g.MAY/FLOW,D
//   ret.*/FLOW -> x.f.f.*/FLOW,N
//   ret.f.*/FLOW -> x.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.NE/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
//   [ret.MAY/FLOW ; x.f.*/FLOW]
//   [ret.MAY/FLOW ; x.f.g.*/FLOW]
//   [ret.f.NE/FLOW ; x.*/FLOW]
// Submitted:
//   ret.MAY/T,D
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.f.f.*/FLOW,N
//   ret.f.*/FLOW -> x.f.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.g.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.f.NE/FLOW,D
//   ret.f.f.*/FLOW -> x.f.f.NE/FLOW,D
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.g.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.g.*/FLOW]
// Submitted:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
```

### Run-5: forward, limit 4

```java
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // x.f.g.MUST/T,N
    Node y = wrapper(x,b1); // y.MAY/T,D, y.f.f.f.g.MUST/T,N
    Node z = wrapper(y,b2); // z.MAY/T,D, z.f.g.MUST/T,N
    Node w = wrapper(z,b3); // w.MAY/T,D, w.f.f.f.g.MUST/T,N
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
//   ZERO -> NormalTarget(id),N (first publication)
```

```java
// Demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.*/FLOW]
//   [x.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.MAY/FLOW ; ret.*/FLOW]
//   [x.f.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.NE/FLOW ; ret.*/FLOW]
//   [x.f.NE/FLOW ; ret.f.*/FLOW]
//   [x.f.g.MAY/FLOW ; ret.*/FLOW]
// Submitted:
//   x.MAY/T,D
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
// Emitted initials:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.$/FLOW,N
//   x.f.g.MUST/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.MAY/FLOW,D
//   x.*/FLOW -> ret.f.MAY/FLOW,D
//   x.*/FLOW -> ret.f.NE/FLOW,D
//   x.*/FLOW -> ret.f.f.*/FLOW,N
//   x.f.*/FLOW -> ret.MAY/FLOW,D
//   x.f.*/FLOW -> ret.f.MAY/FLOW,D
//   x.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.g.MUST/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.g.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.f.*/FLOW -> ret.f.NE/FLOW,D
//   x.f.f.*/FLOW -> ret.f.f.NE/FLOW,D
```

```java
// Demand [Dc ; Dp]:
//   [x.f.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.g.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.f.NE/FLOW ; ret.f.*/FLOW]
//   [x.f.f.NE/FLOW ; ret.f.f.*/FLOW]
// Submitted:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.$/FLOW,N
//   x.f.g.MUST/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
// Emitted initials:
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.$/FLOW,N
//   x.f.g.MUST/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published summaries:
//   none
```

### Run-6: backward, limit 5

```java
// Published observation summary:
//   ZERO -> DemandTarget,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // Backward x: x.MAY/T,D
                            // Producer overlap at x.f.g renews permission.
    Node y = wrapper(x,b1); // Backward y: y.MAY/T,D
    Node z = wrapper(y,b2); // Backward z: z.MAY/T,D
    Node w = wrapper(z,b3); // Backward w: w.MAY/T,D
    observe(w);            // Target-guided ZERO starts the ordinary MAY/T check.
}
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.MAY/FLOW,D
//   ret.*/FLOW -> x.f.MAY/FLOW,D
//   ret.f.*/FLOW -> x.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.g.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.f.MAY/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
//   [ret.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.MAY/FLOW ; x.*/FLOW]
//   [ret.f.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.NE/FLOW ; x.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.g.MUST/FLOW]
//   [ret.f.NE/FLOW ; x.f.g.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.f.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.g.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.f.*/FLOW]
// Submitted:
//   ret.MAY/T,D
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
// Emitted initials:
//   none
```

### Run-7: forward, limit 6

```java
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // x.f.g.MUST/T,N
    Node y = wrapper(x,b1); // y.MAY/T,D, y.f.f.f.g.MUST/T,N
    Node z = wrapper(y,b2); // z.MAY/T,D, z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N
    Node w = wrapper(z,b3); // w.MAY/T,D, w.f.f.f.g.MUST/T,N
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
```

```java
// Demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.*/FLOW]
//   [x.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.MAY/FLOW ; ret.*/FLOW]
//   [x.f.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.g.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.f.MAY/FLOW ; ret.f.*/FLOW]
// Submitted:
//   x.MAY/T,D
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.f.g.MUST/T,N
// Emitted initials:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.$/FLOW,N
//   x.f.g.MUST/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
//   x.f.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.MAY/FLOW,D
//   x.*/FLOW -> ret.f.MAY/FLOW,D
//   x.f.*/FLOW -> ret.MAY/FLOW,D
//   x.f.*/FLOW -> ret.f.MAY/FLOW,D
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.$/FLOW,N
//   x.f.g.MUST/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
//   x.f.f.f.*/FLOW,N
// Emitted initials:
//   none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published summaries:
//   none
```

### Run-8: backward, limit 7

```java
// Published observation summary:
//   ZERO -> DemandTarget,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // Backward x: x.MAY/T,D
                            // Producer overlap at x.f.g renews permission.
    Node y = wrapper(x,b1); // Backward y: y.MAY/T,D
    Node z = wrapper(y,b2); // Backward z: z.MAY/T,D
    Node w = wrapper(z,b3); // Backward w: w.MAY/T,D
    observe(w);            // Target-guided ZERO starts the ordinary MAY/T check.
}
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.MAY/FLOW,D
//   ret.*/FLOW -> x.f.MAY/FLOW,D
//   ret.f.*/FLOW -> x.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.MAY/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
//   [ret.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.MAY/FLOW ; x.*/FLOW]
//   [ret.f.MAY/FLOW ; x.f.*/FLOW]
// Submitted:
//   ret.MAY/T,D
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
// Emitted initials:
//   none
```

### Run-9: forward, limit 8

```java
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // x.f.g.MUST/T,N
    Node y = wrapper(x,b1); // y.MAY/T,D, y.f.f.f.g.MUST/T,N
    Node z = wrapper(y,b2); // z.MAY/T,D, z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N
    Node w = wrapper(z,b3); // w.MAY/T,D, w.f.f.f.g.MUST/T,N, w.f.f.f.f.f.f.f.g.MUST/T,N
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
```

```java
// Demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.*/FLOW]
//   [x.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.MAY/FLOW ; ret.*/FLOW]
//   [x.f.MAY/FLOW ; ret.f.*/FLOW]
// Submitted:
//   x.MAY/T,D
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.f.g.MUST/T,N
// Emitted initials:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Published summaries:
//   x.*/FLOW -> ret.MAY/FLOW,D
//   x.*/FLOW -> ret.f.MAY/FLOW,D
//   x.f.*/FLOW -> ret.MAY/FLOW,D
//   x.f.*/FLOW -> ret.f.MAY/FLOW,D
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.$/FLOW,N
//   x.*/FLOW,N
//   x.f.$/FLOW,N
//   x.f.*/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.$/FLOW,N
//   x.f.f.*/FLOW,N
// Emitted initials:
//   none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published summaries:
//   none
```

### Run-10: backward, limit 9

```java
// Published observation summary:
//   ZERO -> DemandTarget,D
void entry(boolean b1, boolean b2, boolean b3) {
    Node x = produce();     // Backward x: x.MAY/T,D
                            // Producer overlap at x.f.g renews permission.
    Node y = wrapper(x,b1); // Backward y: y.MAY/T,D
    Node z = wrapper(y,b2); // Backward z: z.MAY/T,D
    Node w = wrapper(z,b3); // Backward w: w.MAY/T,D
    observe(w);            // Target-guided ZERO starts the ordinary MAY/T check.
}
// Demand:
//   [Target ; ZERO]
// Submitted:
//   ZERO,N
// Emitted initials:
//   ZERO,N
```

```java
// Published summaries:
//   ret.*/FLOW -> x.MAY/FLOW,D
//   ret.*/FLOW -> x.f.MAY/FLOW,D
//   ret.f.*/FLOW -> x.MAY/FLOW,D
//   ret.f.*/FLOW -> x.f.MAY/FLOW,D
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
//   [ret.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.MAY/FLOW ; x.*/FLOW]
//   [ret.f.MAY/FLOW ; x.f.*/FLOW]
// Submitted:
//   ret.MAY/T,D
// Emitted initials:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
```

```java
// Published summaries:
//   none
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   ret.$/FLOW,N
//   ret.*/FLOW,N
//   ret.f.$/FLOW,N
//   ret.f.*/FLOW,N
//   ret.f.f.$/FLOW,N
//   ret.f.f.*/FLOW,N
// Emitted initials:
//   none
```

For every later forward run, the run-9 annotation repeats exactly. For every later backward run, the run-10 annotation repeats exactly. The field limit grows, but no fact in these mature call packets exceeds eight fields. The induction in section 5 proves this; run-31 survival alone is not the proof.
## 5. Uncapped proof

### Cold start

`ColdMachine.lean` executes the example's two ordinary leaf branches and
wrapper call. It applies C2, one-level plans, common routing masks, native
saved/current roles, per-transfer global cuts, raw-initial C5, paired output
intersection, relative cuts, NORMAL precoverage, executable MAY union and
same-lane uniform retirement. Each owner processes its EXACT queries before
MUST and STAR queries. Prior NORMAL records carry their producer
direction. Every call reply is canonicalized before the next call.

`ColdCertificates.lean` starts with **empty** demand/record stores. For
each run-1 through run-9 it checks the entire final DATA state, one further
worklist round with no change, and both handoff stores. At most three
closure rounds are needed in these finite cold runs. The Python search
generates the proposed witness literals; the Lean kernel independently
checks them against the executable reference machine.

| Completed run | Wrapper outgoing return demand | Choose outgoing return demand | Retained return NORMAL records, wrapper/choose |
| --- | ---: | ---: | --- |
| run-1 | 1 | 2 | 0 / 0 |
| run-2 | 2 | 3 | 0 / 0 |
| run-3 | 4 | 6 | 0 / 1 |
| run-4 | 7 | 4 | 1 / 2 |
| run-5 | 12 | 0 | 2 / 2 |
| run-6 | 6 | 0 | 2 / 2 |
| run-7 | 4 | 0 | 2 / 2 |
| run-8 | 4 | 0 | 2 / 2 |
| run-9 | 4 | 0 | 2 / 2 |

Thus the two NORMAL records are consequences of the cold analysis, not
predefined method summaries. Return geometry is always the ordinary
read-two/write-two geometry. The Java sample compiles independently.

### Stationary DATA frontier

Use a fresh entry/exit frame to compare the two directions. In a forward
run, `a=x,b=ret`; in a backward run, `a=ret,b=x`. The complete mature local
demand set is

```text
K = {
    [a.MAY/FLOW   ; b.*/FLOW],
    [a.MAY/FLOW   ; b.f.*/FLOW],
    [a.f.MAY/FLOW ; b.*/FLOW],
    [a.f.MAY/FLOW ; b.f.*/FLOW]
}
```

For either direction, C2/body/C5 regenerates exactly

```text
E = {
    a.*   -> b.MAY,   D,
    a.*   -> b.f.MAY, D,
    a.f.* -> b.MAY,   D,
    a.f.* -> b.f.MAY, D
} / FLOW

handoff(E) = K                         // Swap endpoints and direction.
```

Caller-visible executable MAY union keeps the root-MAY result for each
premise; the separate refinement view retains all four paired rows. No
extra caller-visible child facts are smuggled into the argument.

`StablePackets.lean` checks the **complete** packet, including the exact
prefix probes and both child kinds. It proves, for every n >= 0 and either
actual domain, that processing at run `9+n`, global limit `8+n`, gives E.
It then proves by induction:

```text
K_0 = K
K_(n+1) = handoff(process(run=9+n, limit=8+n, demand=K_n))

forall n, K_n = K and K_n != empty
```

This is an all-n theorem. It does not infer redundancy from equal counts,
a finite repetition screen or the temporary run-11 limit.

### The caller keeps supplying the actual domain

Write `U_k = x.f^(2k+1).g.MUST/T,N` and `M = x.MAY/T,D`.
Complete, compacted call packets are:

```text
reply(U_0) = {U_1, M}
reply(U_1) = {U_0, U_2, M}
reply(U_2) = {U_1, U_3, M}
reply(M)   = {M}

Forward inputs at the three calls:
    {U_0}, {U_1,M}, {U_0,U_2,M}
Their union is exactly the domain used by the forward packet theorem.
Final forward packet: {U_1,U_3,M}.

Backward:
    {M} -> {M} -> {M} -> {M}
```

These are actual applications to the original offers, with their marks and
layers. They are not a guessed-MUST replacement or a full discarded-suffix
history. `CallerClosure.lean` checks the complete packets against the cold
machine's real saved/current offer operation and proves their global field
cuts are inert at every limit >= 8. The deepest precise result is U_3,
with eight fields. In particular, source support is not postulated anew
at each iteration: reverse calls reach the real producer's region f.g.

### ZERO, observation Targets and continuation

The observer has both NORMAL marked data and M on mature forward runs.
The NORMAL witness supplies its stable NormalTarget id. Independently, M
supplies a fresh `ZERO -> DemandTarget,D`. NORMAL Target does not cover or
remove this anonymous DEMAND Target.

Backward calls return M to the producer point. Its MAY region includes
f.g with T; this is an accepted actual reverse assignment, not a record
replay pretending to be a new assignment. It produces the backward
`ZERO -> DemandTarget,D` and renews the ordinary producer permission.

`TargetClosure.lean` imports the existing `TargetZeroKernel` rather than
inventing a new control rule. Both directions use its paired C5:

```text
incoming row: [Target ; ZERO]
candidate:    ZERO -> DemandTarget,D

Dc Target accepts the actual ZERO premise.
Dp ZERO accepts the actual Target conclusion.
C5 preserves the candidate.
Handoff again gives [Target ; ZERO].
```

The same existing guidance admits the next root ZERO. Both DATA demand
and continuation-relevant Target demand therefore remain nonempty. No
special seed, unanswered-demand retry, terminal publication bypass or
NORMAL+DEMAND NormalTarget composition is added.

### Why the selected compactions do not close this cycle

- **Same-lane uniform coverage:** the current relation's original is STAR
  and its conclusion is MAY. The new rule requires an identical MUST
  original and an NE conclusion. It cannot retire any of E.
- **NORMAL correlated relation subsumption:** W covers known writer
  specializations. It does not cover the unknown-reader MAY result.
  R has premise `a.f.f.*`, which is not a weaker premise than `a.f.*`.
- **FLOW-backed full-mark removal:** E is already FLOW guidance. It is
  not an unprotected concrete-T duplicate awaiting a FLOW provider.
- **Executable MAY coverage:** applied before caller delivery. Local
  paired refinement heads remain under the selected two-view policy.
- **Reply MUST canonicalization:** applied. It cannot delete M by a
  NORMAL descendant MUST: their layers and tail guarantees differ.
- **Bigger field limits:** the mature uncertainty is produced by the
  saved opposite-direction inside match, not by a new field cut.
- **Persisted NormalTarget:** its id is retained and duplicate publication
  is skipped. That rule does not remove a separate DemandTarget.

The residual obligation has made no precision progress. Nevertheless,
every run freshly produces it, so the empty-outgoing-demand stop rule
cannot stop the analysis.

## 6. Validation, scope and receipts

[Lean package](../../spec/lean/proposals/nested-saved-replay-cycle-20261114/README.md)
and [native component test](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/NestedSavedReplayCycleComponentsTest.kt)
are source artifacts in the current working directory; production
is unchanged. The report includes the trace data directly; no separate
repo-local `shape-probe-results` directory is needed.

The proof checker rechecks the previous proposal packages, the existing
ZERO/Target kernel and the new cold/recurrence packages. It rejects holes,
custom/classical axioms and `native_decide`; only `propext` and `Quot.sound`
are allowed. The new package adds **69 audited theorems**. With dependencies and the
reused Target kernel, the receipt contains **542 audited declarations in
32 modules**, with source hashes.

All three native component tests pass. They check the opposite-direction
inside result in both directions, rejection of the real f.g MUST input by
the f.f reader, and NORMAL service for the known f.f child. They do not
claim a native integrated NE run: that proposal has not been implemented
in production. The formal result is a counterexample to the specified AP
reference algorithm within this ordinary positive field-transfer scope,
not a binary correspondence proof for all JVM transfers or schedules.

Latest reached iteration: **run-31** in the exploratory capture. Cold
states are kernel-checked through **run-9**; the complete stationary
forward/backward packets are checked at **run-9/run-10** and proved for
arbitrarily later runs. Native operators use field limit 8, the run-9
geometry; this is not a native run-9 completion. No project scan was run.

Large receipts, compiled proof objects and capture JSON are outside the repo:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
    nested-saved-replay-cycle-20261114/
        nested-cycle.json
        proofs-v5/receipt.json
        native-tests.xml
        native-tests.log
        java/
```

The next design problem is the wrapper's repeated loss of suffix
correlation during saved opposite-direction replay. Any proposed pruning
needs to preserve admitted caller bindings, paired C5 permissions and
future guidance. The existence of one child query is not such a proof.

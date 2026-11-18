# Termination reference with a shared forwarding owner

15 November 2026. Follow [proof-guide.md](../../spec/proof-guide.md).
This validates the [owner-sharing proposal](../design/bidirectional-transparent-forwarder-termination-20261115.md)
against the selected old examples and the
[new nested-call counterexample](bidirectional-nested-saved-replay-nontermination-20261115.md).
Production is unchanged. All programs here are synthetic data-flow examples.

**Result:** the new example naturally stops after **run-9**. The complete
outgoing DATA/Target frontier is empty, and its NORMAL observation remains.
The old required examples retain their previous finite closures/routes.
The unchanged-policy control reaches **run-31** and has a separate uncapped
recurrence proof. A hard iteration limit is not used as evidence.

## 1. Experiment definition

Keep the entire original Java sample and two rules. `produce()` assigns
full T uniformly at `return.f.g`; `observe(a)` checks `a.MAY/T`. `choose`
either returns `x.f.f` or wraps x in two fresh f fields. Entry calls
`wrapper` three times. The wrapper's whole body is:

```java
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
```

The only change is to recognize this certified pure forwarding owner.
Expose choose's stores through its identity frame. Do not run wrapper C2
or C5, create its DATA actor, copy its demand, or apply choose's records
to a wrapper-generated hypothesis. Use the original bounded full-mark
offer at the existing canonical call service.

All other method/block semantics are unchanged: field cuts still emit
NE/DEMAND; C2 emits EXACT/STAR/MUST only; paired C5 remains; opposite
record inside matching remains; same-H uniform coverage and complete
reply folding remain; backward checks still start MAY, not MUST.

The native activation scope is the supplied unary AP context, with alias
expansion absent and no special static effects. The program has no loop,
recursion, cleaner or pass rule. Source-level transparency alone is not
a certificate: the complete call plan, rules and exception routing must
satisfy the guards in the proposal. Uncertified owners keep ordinary analysis.

The constructor, produce and observe bodies retain the control/identity
projection described in the counterexample report. This does not assert
that an API body can never receive an argument fact: unchanged argument
identity lanes are factored out of the return-DATA trace. Rules act at their
entry-caller sites as before. NORMAL ZERO-to-ZERO and unused-input identity
rows add no refinement demand and are not duplicated below. A NORMAL
observation id is first obtained at run-5; the existing persisted-id rule
suppresses later identical publication. It remains available at run-9.

## 2. Complete new reference trace

The program and rules are unchanged. Forward annotations place demand, original offers and initials above declarations, and publications below. Backward annotations reverse that layout. FLOW initials are conditional NORMAL hypotheses. ZERO-only API/constructor control is unchanged from the counterexample report.

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
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   none
// Original logical offers:
//   x.MAY/T,D
//   x.f.NE/T,D
// Own emitted initials: none. choose emits its own C2 family.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.MAY/T,D
//   x.f.NE/T,D
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
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.*/FLOW]
//   [ret.f.NE/FLOW ; x.*/FLOW]
// Original logical offers:
//   ret.MAY/T,D
// Own emitted initials: none. choose emits its own C2 family.
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
//   ret.MAY/T,D
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
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.NE/FLOW ; ret.*/FLOW]
//   [x.f.NE/FLOW ; ret.f.*/FLOW]
// Original logical offers:
//   x.MAY/T,D
//   x.f.MAY/T,D
//   x.f.g.MUST/T,N
// Own emitted initials: none. choose emits its own C2 family.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
```

```java
// Demand [Dc ; Dp]:
//   [x.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.NE/FLOW ; ret.*/FLOW]
//   [x.f.NE/FLOW ; ret.f.*/FLOW]
// Submitted:
//   x.MAY/T,D
//   x.f.MAY/T,D
//   x.f.g.MUST/T,N
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
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   [ret.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.MAY/FLOW ; x.f.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.*/FLOW]
//   [ret.f.NE/FLOW ; x.f.g.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.*/FLOW]
//   [ret.f.f.NE/FLOW ; x.f.g.*/FLOW]
// Original logical offers:
//   ret.MAY/T,D
// Own emitted initials: none. choose emits its own C2 family.
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
//   ret.MAY/T,D
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
    Node y = wrapper(x,b1); // y.f.f.f.g.MUST/T,N
    Node z = wrapper(y,b2); // z.f.g.MUST/T,N, z.f.f.NE/T,D, z.f.f.f.NE/T,D, z.f.f.f.f.NE/T,D
    Node w = wrapper(z,b3); // w.NE/T,D, w.f.NE/T,D, w.f.f.NE/T,D, w.f.f.f.NE/T,D, w.f.f.f.g.MUST/T,N, w.f.f.f.f.NE/T,D
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
//   ZERO -> NormalTarget(id),N (first publication)
```

```java
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   [x.f.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.g.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.f.NE/FLOW ; ret.f.*/FLOW]
//   [x.f.f.NE/FLOW ; ret.f.f.*/FLOW]
// Original logical offers:
//   x.f.g.MUST/T,N
//   x.f.f.NE/T,D
//   x.f.f.f.NE/T,D
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.NE/T,D
// Own emitted initials: none. choose emits its own C2 family.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
```

```java
// Demand [Dc ; Dp]:
//   [x.f.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.g.MAY/FLOW ; ret.f.*/FLOW]
//   [x.f.f.NE/FLOW ; ret.f.*/FLOW]
//   [x.f.f.NE/FLOW ; ret.f.f.*/FLOW]
// Submitted:
//   x.f.g.MUST/T,N
//   x.f.f.NE/T,D
//   x.f.f.f.NE/T,D
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.NE/T,D
// Emitted initials:
//   x.f.$/FLOW,N
//   x.f.g.MUST/FLOW,N
//   x.f.g.*/FLOW,N
//   x.f.f.*/FLOW,N
//   x.f.f.f.*/FLOW,N
Node choose(Node x, boolean down) {
    if (down) return x.f.f;
    Node t = new Node(); t.f = x;
    Node y = new Node(); y.f = t;
    return y;
}
// Published summaries:
//   x.f.f.f.*/FLOW -> ret.f.f.NE/FLOW,D
//   x.f.f.f.*/FLOW -> ret.f.f.f.NE/FLOW,D
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
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   [ret.f.f.NE/FLOW ; x.f.f.f.*/FLOW]
//   [ret.f.f.f.NE/FLOW ; x.f.f.f.*/FLOW]
// Original logical offers:
//   ret.MAY/T,D
// Own emitted initials: none. choose emits its own C2 family.
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
//   [ret.f.f.NE/FLOW ; x.f.f.f.*/FLOW]
//   [ret.f.f.f.NE/FLOW ; x.f.f.f.*/FLOW]
// Submitted:
//   ret.MAY/T,D
// Emitted initials:
//   ret.f.f.*/FLOW,N
//   ret.f.f.f.$/FLOW,N
//   ret.f.f.f.*/FLOW,N
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
    Node y = wrapper(x,b1); // y.f.f.f.g.MUST/T,N
    Node z = wrapper(y,b2); // z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N
    Node w = wrapper(z,b3); // w.f.f.f.g.MUST/T,N, w.f.f.f.f.f.f.NE/T,D
    observe(w);            // A DEMAND witness remains.
}
// Published observation summary:
//   ZERO -> DemandTarget,D
```

```java
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   none
// Original logical offers:
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.f.g.MUST/T,N
// Own emitted initials: none. choose emits its own C2 family.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.f.g.MUST/T,N
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
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   none
// Original logical offers:
//   ret.MAY/T,D
// Own emitted initials: none. choose emits its own C2 family.
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
//   ret.MAY/T,D
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
    Node y = wrapper(x,b1); // y.f.f.f.g.MUST/T,N
    Node z = wrapper(y,b2); // z.f.g.MUST/T,N, z.f.f.f.f.f.g.MUST/T,N
    Node w = wrapper(z,b3); // w.f.f.f.g.MUST/T,N, w.f.f.f.f.f.f.f.g.MUST/T,N
    observe(w);            // NORMAL observations only; id already persisted.
}
// Published observation summary:
//   none
```

```java
// Analysis owner: choose (identity boundary frame).
// Visible demand [Dc ; Dp]:
//   none
// Original logical offers:
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.f.g.MUST/T,N
// Own emitted initials: none. choose emits its own C2 family.
Node wrapper(Node x, boolean down) {
    return choose(x, down);
}
// Own summaries/refinement store: none.
// Callers use the current and persisted choose views.
// No additional C5, delivery or independent wrapper frontier.
```

```java
// Demand [Dc ; Dp]:
//   none
// Submitted:
//   x.f.g.MUST/T,N
//   x.f.f.f.g.MUST/T,N
//   x.f.f.f.f.f.g.MUST/T,N
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

The configured stop rule applies at run-9. choose has no outgoing DATA demand, the proxy has no independent frontier, and entry has no anonymous DEMAND Target. Its persisted NORMAL observation id is retained. No run-11 or other hard limit is used.
## 3. Before versus after

The counterexample's own wrapper had four repeated post-handoff rows
from run-8 onward. Their STAR originals supplied coarse inner-call offers;
the opposite saved reader recreated MAY. Under the proposed directory,
that actor/store does not exist. The callee's own frontier advances:

| Run | Before: wrapper demand | Before: choose demand | After: choose demand | After: final DEMAND actuals |
| --- | ---: | ---: | ---: | ---: |
| run-1 | 1 | 2 | 2 | 1 |
| run-2 | 2 | 3 | 3 | 1 |
| run-3 | 4 | 6 | 6 | 1 |
| run-4 | 7 | 4 | 4 | 1 |
| run-5 | 12 | 0 | 2 | 5 |
| run-6 | 6 | 0 | 0 | 1 |
| run-7 | 4 | 0 | 0 | 1 |
| run-8 | 4 | 0 | 0 | 1 |
| run-9 | 4 | 0 | 0 | 0 |

These are return-DATA refinement rows, not complete engine memory metrics.
The last column contains the actual marked values at the last call: on a
backward run that is the route back to the producer. The proxy has no
independent frontier after the change. Root Target demand is checked too.

The NORMAL writer and reverse-produced reader are derived in cold runs,
not provided as models. At maturity the caller uses them on real offers:

```text
x.f.g.MUST/T,N    -> y.f.f.f.g.MUST/T,N
                  -> z.f.g.MUST/T,N or z.f.f.f.f.f.g.MUST/T,N
                  -> w.f.f.f.g.MUST/T,N or w.f.f.f.f.f.f.f.g.MUST/T,N
```

The f.g input cannot satisfy the f.f reader. There is no coarse wrapper
x.f.STAR query to forget g. The normal cases are thus served by the actual
retained relations. A NORMAL relation still cannot upgrade DEMAND input.

## 4. Full acceptance and proof scope

The checker rechecks all prior proposal/counterexample packages. New proofs
establish the exact forwarding method relation, exception/observation
preservation, identity frame properties, arbitrary certified relay chains,
strict activation guards and unchanged fallback for all old cases.

`ProxyCertificates.lean` checks each entire new run-1 through run-9 state,
a further unchanged worklist round, and both outgoing handoff stores. These
are kernel checks of an executable reference, not trusted Python summaries.
`ProxyAcceptance.lean` checks the complete final DATA and Target frontier
and the NORMAL observation set. It also imports and reapplies the older
method, BB, arbitrary-length reader, protected cleaner, warm-provider,
selected MUST cleaner and wrapper/survivor results. Rejected templates use
the old analyzer for every possible stored state.

| Required reference | New result |
| --- | --- |
| Old method read f.g/write f | Natural run-3 completion; NORMAL observation retained |
| Old inner read/write BBs and enclosing method | Natural run-3 completion; all block frontiers empty |
| Arbitrarily longer reader | Same complete run-3 packet for every reader suffix |
| Ordinary read ff/write ff | Natural run-3 completion |
| Same helper with selected root cleaning | Natural run-3 completion; concrete/H and FLOW/mx lanes retained |
| Standalone selected MUST-preserving cleaner | Natural run-1 completion |
| Wrapper h-read/k-write and exact-root survivor | Existing legal NORMAL routes and nonempty repair unchanged |
| New pure forwarding wrapper, partial uniform f.g producer, three calls | Natural run-9 completion; NORMAL observation retained |

The earlier special-pass intrinsic-MAY program remains excluded from the
selected acceptance set. This proposal does not establish its termination,
or termination for arbitrary nontransparent callers.

No extra transfer semantic is hidden in the proof: eligible wrappers have
no effects of their own. Call arguments retain their slots; the original
inner resolved context and physical port mapping stay valid. The caller's
logical facade and trace frame are preserved. Source permission, reporting,
primitive tracking, H, field writes, matching and tail semantics are not
changed by the directory.

## 5. Validation and iteration positions

- Constructive checker: **55 new theorems**, **597 audited declarations in
  36 modules** with dependencies. No custom/classical axiom, hole or
  `native_decide`; only `propext` and `Quot.sound` are permitted.
- Native components: **12 tests passed**, including three new canonical
  replay tests. They check precise three-call NORMAL outputs, preservation
  of DEMAND support, and the real backward producer route. Existing protected
  growth/provider and opposite-reader tests also pass.
- Latest reached/completed new reference: **run-9/run-9**, without a hard cap.
  Old required references retain **run-1/run-3** completion. The old-policy
  control reaches **run-31** with an uncapped recurrence proof.
- Native forward operators use limit 8, corresponding to run-9; backward
  operators use limit 7, corresponding to run-8. One existing body check is
  a native run-3 component. These are not integrated native NE/proxy scans.
- No new project scan or performance claim is made. Historical project
  positions remain OWASP run-11/11/11, Conductor run-8/7/7 and Stirling-PDF
  run-11/10/9 (reached/completed/accepted-forward).

[Proof package](../../spec/lean/proposals/transparent-forwarder-termination-20261115/README.md)
and [native tests](../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/TransparentForwarderServiceTest.kt)
are in the workspace. The full annotated data are embedded in this report.
Compiled objects, receipts and machine JSON remain outside the repo:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/
    transparent-forwarder-termination-20261115/
        proxy-reference.json
        proofs-v2/receipt.json
        native-tests.log
        native-validation.json
```

This is an AP design reference and a template-equivalence proof. It does
not implement or verify a real JIR recognizer, owner directory or trace
adapter. Those components must discharge the certificate and context/port
checks before production activation. Unsupported cases retain their current
analysis. Production is unchanged.

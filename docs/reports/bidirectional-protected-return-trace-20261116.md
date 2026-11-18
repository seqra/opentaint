# Protected unrelated NORMAL return: complete fact trace

16 November 2026. Synthetic data-flow reachability. Production unchanged.
[Counterexample, root cause and uncapped proof](bidirectional-protected-return-nontermination-20261116.md).

This is the historical full-raw plain-check policy. The selected
[layer-aware repair](../design/bidirectional-layer-aware-point-service-20261116.md)
now naturally stops at **run-5** with the NORMAL observation retained.
[Updated complete fact trace](bidirectional-layer-aware-point-service-trace-20261116.md).
The unchanged native diagnostic remains **run-31/POLICY**.

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
E/mx are empty. H=1 is protected; H=0 is plain. Grouped rows abbreviate separate scalar members.
The shared make owner aggregates all three ordinary call offers. Each call is followed
by a real field read of h. These reads are instructions, not configured pass rules.
Helper submitted facts include the reverse h read in backward runs. Root lines show
the packets after each forward read, or before each reverse read, in code variable names.
All eligible C2 children, current C5 results and saved NORMAL service remain enabled.
The fixed reference controller explicitly models root ZERO/Target permissions.
For forward runs inputs are above each body and outputs below. Backward placement reverses this.
The full cold prefix through run-12 is followed by a proved uncapped two-state cycle.

### Run-1, forward, field limit 1

```java
// Demand [entry | paired output]:
//   unrestricted run-1
// Submitted facts:
//   D,H=0: p.f.NE/T, p.M/T
//   D,H=0: p.M/U
// Emitted initials:
//   D,H=0: p.*/T
//   D,H=0: p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.NE/U
//   p.*/T -> D,H=1: ret.k.MUST/T
//   p.*/U -> D,H=0: ret.h.M/T, ret.h.NE/T
//   p.*/U -> D,H=1: ret.k.MUST/U
```

```java
// Demand control: unrestricted run-1
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.NE/T,D,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.M/U,D,H=0
    Box y = make(x).h; // y.M/T,D,H=0
    Box z = make(y).h; // z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-2, backward, field limit 1

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.NE/T, p.M/T
//   ret.h.$/T -> D,H=0: p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.*/T]
//   [ret.h.NE/U | p.*/T]
//   [ret.k.M/T | p.*/T]
//   [ret.h.M/T | p.*/U]
//   [ret.h.NE/T | p.*/U]
//   [ret.k.M/U | p.*/U]
// Submitted facts:
//   D,H=0: ret.h.M/U
//   D,H=0: ret.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U
//   N,H=0: ret.h.*/FLOW
//   D,H=0: ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=0
    // Backward observation input at z: z.M/U,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D,H=0
```

### Run-3, forward, field limit 2

```java
// Demand [entry | paired output]:
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.h.*/U]
//   [p.f.NE/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.*/T]
// Submitted facts:
//   N,H=0: p.f.g.$/T
//   N,H=0: p.h.MUST/U
//   D,H=0: p.M/U
//   D,H=0: p.M/T
// Emitted initials:
//   N,H=0: p.f.g.$/T
//   D,H=0: p.f.*/T, p.$/T, p.*/T, p.f.$/T
//   N,H=0: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW, p.*/FLOW
//   D,H=0: p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=0: ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.$/U
//   p.h.*/U -> D,H=0: ret.h.h.MUST/T
//   p.f.*/U -> D,H=0: ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T
//   p.$/U -> D,H=0: ret.h.h.MUST/T
//   p.*/U -> D,H=0: ret.h.M/T, ret.h.h.MUST/T
//   p.f.$/U -> D,H=0: ret.h.h.MUST/T
//   p.$/T -> D,H=0: ret.h.h.MUST/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U
//   p.f.$/T -> D,H=0: ret.h.h.MUST/U
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It is disjoint from h/U. Both bodyClosed and the full-raw plain scan still reject it.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0; x.M/U,D,H=0
    Box y = make(x).h; // y.M/T,D,H=0
    Box z = make(y).h; // z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.g.NE/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.f.*/T -> D,H=0: p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D,H=0: p.h.M/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.h.h.*/T -> D,H=0: p.h.M/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.h.$/T -> D,H=0: p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.f.*/T, p.*/T]
//   [ret.h.h.M/U | p.f.*/T, p.$/T, p.*/T, p.f.$/T]
//   [ret.h.h.M/T | p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U]
//   [ret.h.$/T | p.f.*/U]
//   [ret.h.M/T | p.f.*/U, p.*/U]
//   [ret.h.$/U | p.f.*/T]
// Submitted facts:
//   D,H=0: ret.h.M/U
//   D,H=0: ret.h.f.g.$/T, ret.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N,H=0: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW
//   D,H=0: ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=0
    // Backward observation input at z: z.M/U,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D,H=0
```

### Run-5, forward, field limit 4

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.NE/U | ret.h.f.*/T, ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.NE/U | ret.h.f.*/T, ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.M/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.M/U | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.M/U | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.$/U | ret.h.h.$/T, ret.h.h.*/T]
// Submitted facts:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.M/U
//   D,H=0: p.M/T
// Emitted initials:
//   N,H=0: p.f.g.$/T, p.h.$/T
//   N,H=0: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D,H=0: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.h.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=0: ret.h.h.MUST/U, ret.h.h.$/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D,H=0: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.*/U -> D,H=0: ret.h.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
//   p.f.*/U -> D,H=0: ret.h.f.M/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.$/T
//   p.h.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D,H=0: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.$/U -> D,H=0: ret.h.h.MUST/T, ret.h.h.$/T
//   p.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D,H=0: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
//   p.h.*/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.*/T -> D,H=0: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It is disjoint from h/U. Both bodyClosed and the full-raw plain scan still reject it.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0; x.h.$/U,N,H=0; x.M/U,D,H=0
    Box y = make(x).h; // y.h.$/T,N,H=0; y.h.MUST/T,N,H=0; y.M/T,D,H=0
    Box z = make(y).h; // z.h.MUST/U,N,H=0; z.h.$/U,N,H=0; z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-6, backward, field limit 5

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.g.NE/T, p.f.g.g.M/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D,H=0: p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D,H=0: p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.f.g.$/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.f.g.$/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D,H=0: p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.$/T -> D,H=0: p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.f.*/T, p.f.g.*/T, p.*/T]
//   [ret.h.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T]
//   [ret.h.h.M/T | p.h.*/U, p.h.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.f.g.$/U, p.$/U, p.*/U]
//   [ret.h.h.$/T | p.h.*/U, p.h.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.f.g.$/U, p.$/U, p.*/U]
//   [ret.h.f.M/T | p.f.g.*/U, p.f.*/U]
//   [ret.h.$/T | p.f.g.*/U, p.f.*/U]
//   [ret.h.M/T | p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.h.$/U | p.f.g.*/T, p.f.*/T]
// Submitted facts:
//   D,H=0: ret.h.M/U, ret.h.h.M/U
//   D,H=0: ret.h.f.g.$/T, ret.h.h.$/T, ret.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N,H=0: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW
//   D,H=0: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=0
    // Backward observation input at z: z.M/U,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D,H=0
```

### Run-7, forward, field limit 6

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.h.M/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.M/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.M/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.$/T, ret.h.*/T, ret.h.h.*/T]
//   [p.f.g.NE/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.$/T, ret.h.*/T, ret.h.h.*/T]
//   [p.f.NE/U | ret.h.f.*/T, ret.h.h.$/T, ret.h.$/T, ret.h.*/T, ret.h.h.*/T]
//   [p.h.M/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.M/U | ret.h.h.$/T, ret.h.*/T, ret.h.h.*/T]
//   [p.f.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.M/U | ret.h.h.$/T, ret.h.*/T, ret.h.h.*/T]
//   [p.f.g.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.M/U | ret.h.h.$/T, ret.h.*/T, ret.h.h.*/T]
// Submitted facts:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.M/U
//   D,H=0: p.M/T
// Emitted initials:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D,H=0: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.h.MUST/T -> N,H=0: ret.h.h.$/U, ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.*/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.$/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T
//   p.f.g.g.*/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T
//   p.f.g.*/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.M/T, ret.h.$/T
//   p.f.*/U -> D,H=0: ret.h.f.M/T, ret.h.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.M/T, ret.h.$/T
//   p.h.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.g.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D,H=0: ret.h.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.M/T
//   p.f.g.*/T -> D,H=0: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.g.g.$/T -> D,H=0: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.*/T -> D,H=0: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It is disjoint from h/U. Both bodyClosed and the full-raw plain scan still reject it.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0; x.h.$/U,N,H=0; x.M/U,D,H=0
    Box y = make(x).h; // y.h.$/T,N,H=0; y.h.MUST/T,N,H=0; y.M/T,D,H=0
    Box z = make(y).h; // z.h.$/U,N,H=0; z.h.MUST/U,N,H=0; z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-8, backward, field limit 7

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.g.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.h.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.h.M/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.f.g.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.h.f.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.h.f.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.h.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.h.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.h.$/U | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
// Submitted facts:
//   D,H=0: ret.h.M/U, ret.h.h.M/U
//   D,H=0: ret.h.f.g.$/T, ret.h.h.M/T, ret.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N,H=0: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.g.*/FLOW
//   D,H=0: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=0
    // Backward observation input at z: z.M/U,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D,H=0
```

### Run-9, forward, field limit 8

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.h.M/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.M/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.$/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.h.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.$/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T]
//   [p.f.g.g.M/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T]
//   [p.f.g.NE/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.$/T, ret.h.*/T]
//   [p.f.NE/U | ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.$/T, ret.h.*/T]
//   [p.h.M/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.M/U | ret.h.h.$/T, ret.h.h.*/T, ret.h.*/T]
//   [p.f.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.M/U | ret.h.h.$/T, ret.h.h.*/T, ret.h.*/T]
//   [p.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.M/U | ret.h.h.$/T, ret.h.h.*/T, ret.h.*/T]
// Submitted facts:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.M/U
//   D,H=0: p.M/T
// Emitted initials:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D,H=0: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.h.MUST/T -> N,H=0: ret.h.h.$/U, ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.*/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.$/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.g.*/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.*/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.M/T, ret.h.$/T
//   p.f.*/U -> D,H=0: ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T, ret.h.$/T
//   p.h.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.g.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D,H=0: ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T
//   p.f.g.*/T -> D,H=0: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.g.g.$/T -> D,H=0: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.*/T -> D,H=0: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It is disjoint from h/U. Both bodyClosed and the full-raw plain scan still reject it.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0; x.h.$/U,N,H=0; x.M/U,D,H=0
    Box y = make(x).h; // y.h.$/T,N,H=0; y.h.MUST/T,N,H=0; y.M/T,D,H=0
    Box z = make(y).h; // z.h.$/U,N,H=0; z.h.MUST/U,N,H=0; z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-10, backward, field limit 9

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.g.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.h.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.h.M/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.f.g.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.h.f.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.h.f.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.h.f.g.M/T | p.f.g.g.$/U, p.f.g.g.*/U]
//   [ret.h.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.h.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.h.$/U | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
// Submitted facts:
//   D,H=0: ret.h.M/U, ret.h.h.M/U
//   D,H=0: ret.h.f.g.$/T, ret.h.h.M/T, ret.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N,H=0: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.g.*/FLOW
//   D,H=0: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=0
    // Backward observation input at z: z.M/U,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D,H=0
```

### Run-11, forward, field limit 10

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.h.M/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.M/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.$/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.h.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.$/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.M/T | ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U]
//   [p.f.g.g.$/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T]
//   [p.f.g.g.M/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T]
//   [p.f.g.NE/U | ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.$/T, ret.h.*/T]
//   [p.f.NE/U | ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.$/T, ret.h.*/T]
//   [p.h.M/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.M/U | ret.h.h.$/T, ret.h.h.*/T, ret.h.*/T]
//   [p.f.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.M/U | ret.h.h.$/T, ret.h.h.*/T, ret.h.*/T]
//   [p.$/U | ret.h.h.$/T, ret.h.h.*/T]
//   [p.M/U | ret.h.h.$/T, ret.h.h.*/T, ret.h.*/T]
// Submitted facts:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.M/U
//   D,H=0: p.M/T
// Emitted initials:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D,H=0: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N,H=0: p.h.MUST/U, p.h.$/U
//   D,H=0: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.h.MUST/T -> N,H=0: ret.h.h.$/U, ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.*/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.$/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.g.*/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.*/U -> D,H=0: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.M/T, ret.h.$/T
//   p.f.*/U -> D,H=0: ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T, ret.h.$/T
//   p.h.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.g.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/U -> D,H=0: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D,H=0: ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T
//   p.f.g.*/T -> D,H=0: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.g.g.$/T -> D,H=0: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.*/T -> D,H=0: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D,H=0: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.$/T -> D,H=0: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It is disjoint from h/U. Both bodyClosed and the full-raw plain scan still reject it.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0; x.h.$/U,N,H=0; x.M/U,D,H=0
    Box y = make(x).h; // y.h.$/T,N,H=0; y.h.MUST/T,N,H=0; y.M/T,D,H=0
    Box z = make(y).h; // z.h.$/U,N,H=0; z.h.MUST/U,N,H=0; z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-12, backward, field limit 11

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D,H=0: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.g.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.h.$/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign T to r.k.MUST; H=1.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign U to r.k.MUST; H=1.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.h.M/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.f.g.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.h.f.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.h.f.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.h.f.g.M/T | p.f.g.g.$/U, p.f.g.g.*/U]
//   [ret.h.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.h.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.h.$/U | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
// Submitted facts:
//   D,H=0: ret.h.M/U, ret.h.h.M/U
//   D,H=0: ret.h.f.g.$/T, ret.h.h.M/T, ret.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N,H=0: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.g.*/FLOW
//   D,H=0: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=0
    // Backward observation input at z: z.M/U,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D,H=0
```

## Every later pair

For every n >= 0, history(11+2n) equals the complete run-11 state and
history(12+2n) equals the complete run-12 state. Both frontiers are nonempty.
Forward DemandTarget and backward entry-marking permission remain active.
The proof covers arbitrary later budgets, not only the native run-31 capture.
Within-run fixed points are checked separately; this is not worklist starvation.

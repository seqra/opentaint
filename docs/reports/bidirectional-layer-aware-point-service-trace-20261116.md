# NORMAL layer and protection: repaired fact trace

16 November 2026. Synthetic data-flow reachability. Production unchanged.
[Selected repair, proofs and limits](../design/bidirectional-layer-aware-point-service-20261116.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
E/mx are empty. H=1 is protected; H=0 is plain. Grouped rows abbreviate separate scalar members.
The shared make owner aggregates all three ordinary call offers. Each call is followed
by a real field read of h. These reads are instructions, not configured pass rules.
Helper submitted facts include the reverse h read in backward runs. Root lines show
the packets after each forward read, or before each reverse read, in code variable names.
All eligible C2 children, current C5 results and saved NORMAL service remain enabled.
The fixed reference controller explicitly models root ZERO/Target permissions.
For forward runs inputs are above each body and outputs below. Backward placement reverses this.
The cold reference stops naturally at run-5. Every later run is proved quiet.

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
//   D,H=0: p.h.MUST/T
// Emitted initials:
//   N,H=0: p.f.g.$/T
//   D,H=0: p.f.*/T, p.h.*/T
//   N,H=0: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW
//   D,H=0: p.h.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
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
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.h.MUST/U
//   p.h.*/U -> D,H=0: ret.h.h.MUST/T
//   p.h.*/T -> D,H=0: ret.h.h.MUST/U
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It stays NORMAL+H=1 in the full closure; the h reply still needs plain NORMAL service.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0
    Box y = make(x).h; // y.h.MUST/T,D,H=0
    Box z = make(y).h; // z.h.MUST/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D,H=0: p.f.g.NE/T
//   ret.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T
//   ret.h.h.$/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T
//   ret.h.h.*/U -> D,H=0: p.f.g.NE/T, p.f.M/T, p.h.M/T
//   ret.h.h.$/T -> D,H=0: p.h.M/U
//   ret.h.h.*/T -> D,H=0: p.h.M/U
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
//   [ret.h.M/U | p.f.*/T]
//   [ret.h.h.M/U | p.f.*/T, p.h.*/T]
//   [ret.h.h.M/T | p.h.*/U]
// Submitted facts:
//   D,H=0: ret.h.M/U, ret.h.h.M/U
//   D,H=0: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.M/T
// Emitted initials:
//   D,H=0: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N,H=0: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.$/FLOW
//   D,H=0: ret.h.h.$/T, ret.h.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.f.M/T,D,H=0; a.h.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.h.M/U,D,H=0
    Box z = make(y).h; // backward requirements at y: y.f.M/T,D,H=0; y.h.M/T,D,H=0
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
//   [p.h.M/T | ret.h.h.$/U, ret.h.h.*/U]
//   [p.h.M/U | ret.h.h.$/T, ret.h.h.*/T]
// Submitted facts:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.h.MUST/U, p.h.$/U
// Emitted initials:
//   N,H=0: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N,H=0: p.f.$/FLOW
//   N,H=0: p.h.MUST/U, p.h.$/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
//   p.h.$/U
//   p.h.$/T
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
// Published qualified DEMAND summaries: none
// Unpublished raw fine-query witness: p.f.g.$/T -> ret.k.MUST/T,N,H=1.
// It stays NORMAL+H=1 in the full closure; the h reply still needs plain NORMAL service.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N,H=0; x.h.$/U,N,H=0
    Box y = make(x).h; // y.h.$/T,N,H=0; y.h.MUST/T,N,H=0
    Box z = make(y).h; // z.h.$/U,N,H=0; z.h.MUST/U,N,H=0
    // Observe CM(z.M,U).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```

### Run-6, backward, field limit 5

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries: none
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
// Demand [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: none.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: none
    Box y = make(x).h; // backward requirements at x: none
    Box z = make(y).h; // backward requirements at y: none
    // Backward observation input at z: none
}
// Demand control: inactive
// Submitted ZERO / emitted ZERO: none
// Backward observation input at z: none
```

## Uncapped quiet suffix

For every n >= 0, history(n+6) equals the complete quiet run-6 state.
The NORMAL observation is retained and neither DATA nor Target demand revives.
This is an induction result for the uncapped schedule; within-run quiescence is checked too.

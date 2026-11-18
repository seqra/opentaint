# Mark-scoped NORMAL service: checked run trace

16 November 2026. Synthetic data-flow reachability. Production unchanged.
[Contract, proof scope and results](bidirectional-mark-scoped-point-service-20261116.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
All H are plain and E/mx empty. Paired rows and summary lines with multiple
outputs list separate scalar members. Saved NORMAL service remains available.
The shared make owner aggregates all three actual call offers. The root controller
models typed ZERO/Target permissions. Inactive bodies are printed for alignment only.
For forward runs inputs are above the body and outputs below. Backward placement is reversed.

## Mark-scoped completion usable immediately after native service applies

### Run-1, forward, field limit 1

```java
// Demand [entry | paired output]:
//   unrestricted run-1
// Submitted facts:
//   D: p.f.NE/T, p.M/T
//   D: p.M/U, p.h.M/U
//   D: p.k.MUST/V
// Emitted initials:
//   D: p.*/T
//   D: p.*/U
//   D: p.*/V
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.k.MUST/V
//   p.*/U -> D: ret.M/T, ret.h.MUST/T
//   p.*/V -> D: ret.h.M/U
```

```java
// Demand control: unrestricted run-1
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.NE/T,D
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.M/U,D; x.k.MUST/V,D
    Box y = make(x); // y.M/T,D; y.h.M/U,D
    Box z = make(y); // z.M/U,D; z.k.MUST/V,D; z.M/T,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-2, backward, field limit 1

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.$/U -> D: p.f.NE/T
//   ret.*/U -> D: p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.NE/T, p.M/T, p.s.M/V
//   ret.h.*/U -> D: p.f.NE/T, p.M/T, p.s.M/V
//   ret.$/T -> D: p.f.NE/U
//   ret.*/T -> D: p.f.NE/U, p.M/U
//   ret.h.$/T -> D: p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.M/U | p.*/T]
//   [ret.h.M/U | p.*/T, p.*/V]
//   [ret.k.M/V | p.*/T]
//   [ret.M/T | p.*/U]
//   [ret.h.M/T | p.*/U]
// Submitted facts:
//   D: ret.M/U
//   D: ret.M/T
//   D: ret.s.M/V
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW
//   D: ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published source permission: yes.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a); // backward requirements at a: a.M/T,D; a.s.M/V,D
    Box y = make(x); // backward requirements at x: x.M/U,D
    Box z = make(y); // backward requirements at y: y.M/T,D; y.s.M/V,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
```

### Run-3, forward, field limit 2

```java
// Demand [entry | paired output]:
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.s.M/V | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/U | ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.*/T, ret.h.$/T, ret.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
// Emitted initials:
//   N: p.f.g.$/T, p.h.$/T
//   D: p.f.*/T, p.h.*/T
//   N: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW
//   D: p.h.*/U
//   N: p.h.$/U
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.$/U -> N: ret.h.MUST/T, ret.h.$/T
//   p.h.$/T -> N: ret.h.MUST/U, ret.h.$/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.h.*/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
// Raw ret.k.MUST/V remains unadmitted; its missing service does not certify V.
// It no longer blocks complete U terminal service. Internal NORMAL closure is still required.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N
    Box y = make(x); // y.h.MUST/T,N; y.h.$/T,N
    Box z = make(y); // z.h.MUST/U,N; z.h.$/U,N
    // Observe CM(z.M,U).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.M/U | p.f.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T]
//   [ret.h.M/T | p.h.*/U]
//   [ret.h.$/T | p.h.*/U]
// Submitted facts: none
// Emitted initials: none
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
```

```java
// Published source permission: none.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a); // backward requirements at a: none
    Box y = make(x); // backward requirements at x: none
    Box z = make(y); // backward requirements at y: none
    // Backward observation input at z: none
}
// Demand control: inactive
// Submitted ZERO / emitted ZERO: none
// Backward observation input at z: none
```

### Run-5, forward, field limit 4

```java
// Demand [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries: none
```

```java
// Demand control: inactive
// Submitted ZERO / emitted ZERO: none
// Entry DATA: none
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // none
    Box y = make(x); // none
    Box z = make(y); // none
    // Observe CM(z.M,U).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```

## Mark-scoped completion usable only after handoff

The earlier DemandTarget remains emitted. This separate execution naturally stops at run-7.

### Run-1, forward, field limit 1

```java
// Demand [entry | paired output]:
//   unrestricted run-1
// Submitted facts:
//   D: p.f.NE/T, p.M/T
//   D: p.M/U, p.h.M/U
//   D: p.k.MUST/V
// Emitted initials:
//   D: p.*/T
//   D: p.*/U
//   D: p.*/V
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.k.MUST/V
//   p.*/U -> D: ret.M/T, ret.h.MUST/T
//   p.*/V -> D: ret.h.M/U
```

```java
// Demand control: unrestricted run-1
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.NE/T,D
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.M/U,D; x.k.MUST/V,D
    Box y = make(x); // y.M/T,D; y.h.M/U,D
    Box z = make(y); // z.M/U,D; z.k.MUST/V,D; z.M/T,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-2, backward, field limit 1

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.$/U -> D: p.f.NE/T
//   ret.*/U -> D: p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.NE/T, p.M/T, p.s.M/V
//   ret.h.*/U -> D: p.f.NE/T, p.M/T, p.s.M/V
//   ret.$/T -> D: p.f.NE/U
//   ret.*/T -> D: p.f.NE/U, p.M/U
//   ret.h.$/T -> D: p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.M/U | p.*/T]
//   [ret.h.M/U | p.*/T, p.*/V]
//   [ret.k.M/V | p.*/T]
//   [ret.M/T | p.*/U]
//   [ret.h.M/T | p.*/U]
// Submitted facts:
//   D: ret.M/U
//   D: ret.M/T
//   D: ret.s.M/V
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW
//   D: ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published source permission: yes.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a); // backward requirements at a: a.M/T,D; a.s.M/V,D
    Box y = make(x); // backward requirements at x: x.M/U,D
    Box z = make(y); // backward requirements at y: y.M/T,D; y.s.M/V,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
```

### Run-3, forward, field limit 2

```java
// Demand [entry | paired output]:
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.s.M/V | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/U | ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.*/T, ret.h.$/T, ret.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.$/T
//   D: p.f.*/T, p.$/T, p.*/T, p.f.$/T, p.h.*/T
//   N: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW, p.*/FLOW
//   D: p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U
//   N: p.h.$/U
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.$/U -> N: ret.h.MUST/T, ret.h.$/T
//   p.h.$/T -> N: ret.h.MUST/U, ret.h.$/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.f.*/U -> D: ret.$/T, ret.M/T, ret.h.MUST/T, ret.h.$/T, ret.h.M/T
//   p.$/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.*/U -> D: ret.M/T, ret.h.MUST/T, ret.h.$/T, ret.h.M/T
//   p.f.$/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
// Raw ret.k.MUST/V remains unadmitted; its missing service does not certify V.
// It no longer blocks complete U terminal service. Internal NORMAL closure is still required.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.h.MUST/U,N; x.M/U,D; x.h.$/U,N
    Box y = make(x); // y.M/T,D; y.h.MUST/T,N; y.h.$/T,N
    Box z = make(y); // z.M/U,D; z.h.MUST/U,N; z.h.$/U,N
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.$/U -> D: p.f.g.NE/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T, p.h.M/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T, p.h.M/T
//   ret.f.*/T -> D: p.f.g.NE/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.h.*/T -> D: p.h.M/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.$/T -> D: p.f.g.NE/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.M/U | p.f.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.$/T, p.*/T, p.f.$/T, p.h.*/T]
//   [ret.h.$/U | p.f.*/T, p.$/T, p.*/T, p.f.$/T, p.h.*/T]
//   [ret.h.M/T | p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U]
//   [ret.h.$/T | p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U]
//   [ret.$/T | p.f.*/U]
//   [ret.M/T | p.f.*/U, p.*/U]
//   [ret.$/U | p.f.*/T]
// Submitted facts:
//   D: ret.M/U, ret.h.$/U
//   D: ret.f.g.$/T, ret.h.$/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.*/FLOW, ret.$/FLOW
//   D: ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
```

```java
// Published source permission: yes.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a); // backward requirements at a: a.M/T,D
    Box y = make(x); // backward requirements at x: x.M/U,D
    Box z = make(y); // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
```

### Run-5, forward, field limit 4

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.$/T | ret.h.$/U, ret.h.*/U]
//   [p.h.M/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.NE/U | ret.f.*/T, ret.h.$/T, ret.$/T, ret.*/T, ret.h.*/T]
//   [p.f.NE/U | ret.f.*/T, ret.h.$/T, ret.$/T, ret.*/T, ret.h.*/T]
//   [p.h.M/U | ret.h.$/T, ret.h.*/T]
//   [p.f.M/U | ret.h.$/T, ret.*/T, ret.h.*/T]
//   [p.$/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.$/T, ret.*/T, ret.h.*/T]
//   [p.f.$/U | ret.h.$/T, ret.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW
//   D: p.f.*/T, p.h.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.MUST/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.$/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.MUST/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.$/T -> N: ret.h.MUST/U, ret.h.$/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.h.*/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
// Raw ret.k.MUST/V remains unadmitted; its missing service does not certify V.
// It no longer blocks complete U terminal service. Internal NORMAL closure is still required.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N
    Box z = make(y); // z.h.MUST/U,N; z.h.$/U,N
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
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.M/U | p.f.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T]
//   [ret.h.$/T | p.h.*/U]
//   [ret.h.M/T | p.h.*/U]
// Submitted facts: none
// Emitted initials: none
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
```

```java
// Published source permission: none.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a); // backward requirements at a: none
    Box y = make(x); // backward requirements at x: none
    Box z = make(y); // backward requirements at y: none
    // Backward observation input at z: none
}
// Demand control: inactive
// Submitted ZERO / emitted ZERO: none
// Backward observation input at z: none
```

### Run-7, forward, field limit 6

```java
// Demand [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
// Whole complete keys:
//   p.h.$/U
// Mark-scoped complete keys:
//   p.f.g.$/T => U
//   p.h.$/T => U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    // CM(p.M,T)       => assign V to r.k.MUST.
    // CM(p.s.M,V)     => assign U to r.h.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries: none
```

```java
// Demand control: inactive
// Submitted ZERO / emitted ZERO: none
// Entry DATA: none
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // none
    Box y = make(x); // none
    Box z = make(y); // none
    // Observe CM(z.M,U).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```

## Uncapped quiet suffix

Every run >= 6 is quiet in the first execution; every run >= 8 is quiet in the delayed
execution. These are constructive induction results, independent of a hard iteration limit.

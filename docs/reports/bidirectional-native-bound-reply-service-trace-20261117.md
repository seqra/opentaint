# Native-bound NORMAL service: complete cold traces

17 November 2026. Synthetic data-flow reachability. Production unchanged.
[Selected rule and proof scope](../design/bidirectional-native-bound-reply-service-20261117.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
H is literal protection. E/mx are empty in these two programs.
Each make owner aggregates three ordinary calls, followed by a read of h.
Forward annotations put demand, offers and initials before the body;
backward annotations put them after it. Summaries use the opposite side.
NORMAL source records are persisted. DemandTarget effects are accumulated;
no emitted Target is canceled. The new selector changes only current
DEMAND DATA delivery after complete native-bound NORMAL service.

## Protected exact input: natural completion at run-7

### Run-1, forward, field limit 1

```java
// Demand [entry | paired output]:
//   unrestricted run-1
// Submitted facts:
//   D: p.f.NE/T, p.M/T
// Emitted initials:
//   D: p.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.*/T -> D,H=1: ret.h.M/T, ret.h.NE/T
```

```java
// Demand control: unrestricted run-1
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.NE/T,D,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.M/T,D,H=1
    Box y = make(x).h; // y.M/T,D,H=1
    Box z = make(y).h; // z.M/T,D,H=1
    // Observe CM(z.M,T).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-2, backward, field limit 1

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/T -> D,H=1: p.f.NE/T
//   ret.h.*/T -> D,H=1: p.f.NE/T, p.M/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/T | p.*/T]
//   [ret.h.NE/T | p.*/T]
// Submitted facts:
//   D: ret.h.M/T
// Emitted initials:
//   D: ret.h.$/T, ret.h.*/T
//   N: ret.h.*/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

### Run-3, forward, field limit 2

```java
// Demand [entry | paired output]:
//   [p.f.NE/T | ret.h.$/T, ret.h.*/T]
//   [p.M/T | ret.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T
//   D: p.f.*/T, p.$/T, p.*/T, p.f.$/T
//   N: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.*/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.f.g.$/T -> D,H=1: ret.h.f.NE/T
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.f.NE/T, ret.h.$/T
//   p.$/T -> D,H=1: ret.h.f.NE/T
//   p.*/T -> D,H=1: ret.h.M/T, ret.h.f.NE/T
//   p.f.$/T -> D,H=1: ret.h.f.NE/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.M/T,D,H=1
    Box y = make(x).h; // y.M/T,D,H=1
    Box z = make(y).h; // z.M/T,D,H=1
    // Observe CM(z.M,T).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.f.*/T -> D,H=1: p.f.g.$/T, p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.$/T -> D,H=1: p.f.g.NE/T, p.f.NE/T
//   ret.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.f.$/T -> D,H=1: p.f.g.NE/T, p.f.NE/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.f.NE/T | p.f.g.$/T, p.f.*/T, p.$/T, p.*/T, p.f.$/T]
//   [ret.h.M/T | p.f.*/T, p.*/T]
//   [ret.h.$/T | p.f.*/T]
// Submitted facts:
//   D: ret.h.M/T
// Emitted initials:
//   D: ret.h.f.*/T, ret.h.$/T, ret.h.*/T, ret.h.f.$/T
//   N: ret.h.f.*/FLOW, ret.h.*/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

### Run-5, forward, field limit 4

```java
// Demand [entry | paired output]:
//   [p.f.g.$/T | ret.h.f.*/T]
//   [p.f.g.NE/T | ret.h.$/T, ret.h.*/T, ret.h.f.$/T, ret.h.f.*/T]
//   [p.f.M/T | ret.h.*/T, ret.h.f.*/T]
//   [p.$/T | ret.h.f.*/T]
//   [p.f.NE/T | ret.h.$/T, ret.h.*/T, ret.h.f.$/T, ret.h.f.*/T]
//   [p.M/T | ret.h.*/T, ret.h.f.*/T]
//   [p.f.$/T | ret.h.f.*/T]
// Submitted facts:
//   N: p.f.g.$/T
// Emitted initials:
//   N: p.f.g.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW
//   D: p.f.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=1: ret.h.f.g.$/T
// Published qualified DEMAND summaries:
//   p.f.g.$/T -> D,H=1: ret.h.f.NE/T
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.f.NE/T, ret.h.f.M/T, ret.h.f.g.$/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.f.g.$/T,N,H=1
    Box y = make(x).h; // y.f.g.$/T,N,H=1
    Box z = make(y).h; // z.f.g.$/T,N,H=1
    // Observe CM(z.M,T).
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
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.f.NE/T | p.f.g.$/T, p.f.*/T]
//   [ret.h.M/T | p.f.*/T]
//   [ret.h.f.M/T | p.f.*/T]
//   [ret.h.f.g.$/T | p.f.*/T]
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

### Run-7, forward, field limit 6

```java
// Demand [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$.  // H=1
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
    Box x = make(a).h; // none
    Box y = make(x).h; // none
    Box z = make(y).h; // none
    // Observe CM(z.M,T).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```

## Uniform input control: natural completion at run-9

### Run-1, forward, field limit 1

```java
// Demand [entry | paired output]:
//   unrestricted run-1
// Submitted facts:
//   D: p.f.NE/T, p.M/T
//   D: p.M/U
// Emitted initials:
//   D: p.*/T
//   D: p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.NE/U
//   p.*/U -> D,H=0: ret.h.M/T, ret.h.NE/T
```

```java
// Demand control: unrestricted run-1
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.NE/T,D,H=0
void root(Box a) { // Entry marking: T uniformly at a.f.g.MUST.
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
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.*/T]
//   [ret.h.NE/U | p.*/T]
//   [ret.h.M/T | p.*/U]
//   [ret.h.NE/T | p.*/U]
// Submitted facts:
//   D: ret.h.M/U
//   D: ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U
//   N: ret.h.*/FLOW
//   D: ret.h.$/T, ret.h.*/T
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
//   N: p.f.g.MUST/T
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   D: p.f.g.*/T, p.f.*/T, p.$/T, p.*/T, p.f.$/T
//   N: p.f.g.*/FLOW, p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.*/FLOW
//   D: p.f.*/U, p.$/U, p.*/U, p.f.$/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.f.g.*/T -> D,H=0: ret.h.f.NE/U
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.f.NE/U, ret.h.$/U
//   p.f.*/U -> D,H=0: ret.h.$/T, ret.h.M/T, ret.h.f.NE/T
//   p.$/U -> D,H=0: ret.h.f.NE/T
//   p.*/U -> D,H=0: ret.h.M/T, ret.h.f.NE/T
//   p.f.$/U -> D,H=0: ret.h.f.NE/T
//   p.$/T -> D,H=0: ret.h.f.NE/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.f.NE/U
//   p.f.$/T -> D,H=0: ret.h.f.NE/U
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.MUST/T,N,H=0
void root(Box a) { // Entry marking: T uniformly at a.f.g.MUST.
    Box x = make(a).h; // x.M/U,D,H=0
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
//   ret.h.f.*/U -> D,H=0: p.f.g.M/T, p.f.h.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.$/U -> D,H=0: p.f.h.NE/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.h.NE/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.f.$/U -> D,H=0: p.f.h.NE/T, p.f.NE/T
//   ret.h.$/T -> D,H=0: p.f.h.NE/U, p.f.NE/U
//   ret.h.*/T -> D,H=0: p.f.h.NE/U, p.f.M/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D,H=0: p.f.h.NE/U, p.f.NE/U
//   ret.h.f.*/T -> D,H=0: p.f.h.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.f.NE/U | p.f.g.*/T, p.f.*/T, p.$/T, p.*/T, p.f.$/T]
//   [ret.h.M/U | p.f.*/T, p.*/T]
//   [ret.h.$/T | p.f.*/U]
//   [ret.h.M/T | p.f.*/U, p.*/U]
//   [ret.h.f.NE/T | p.f.*/U, p.$/U, p.*/U, p.f.$/U]
//   [ret.h.$/U | p.f.*/T]
// Submitted facts:
//   D: ret.h.M/U
//   D: ret.h.M/T
// Emitted initials:
//   D: ret.h.f.*/U, ret.h.$/U, ret.h.*/U, ret.h.f.$/U
//   N: ret.h.f.*/FLOW, ret.h.*/FLOW
//   D: ret.h.$/T, ret.h.*/T, ret.h.f.$/T, ret.h.f.*/T
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
//   [p.f.g.M/T | ret.h.f.*/U]
//   [p.f.h.NE/T | ret.h.$/U, ret.h.*/U, ret.h.f.$/U, ret.h.f.*/U]
//   [p.f.M/T | ret.h.*/U, ret.h.f.*/U]
//   [p.$/T | ret.h.f.*/U]
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U, ret.h.f.$/U, ret.h.f.*/U]
//   [p.M/T | ret.h.*/U, ret.h.f.*/U]
//   [p.f.$/T | ret.h.f.*/U]
//   [p.f.h.NE/U | ret.h.$/T, ret.h.*/T, ret.h.f.$/T, ret.h.f.*/T]
//   [p.f.M/U | ret.h.*/T, ret.h.f.*/T]
//   [p.$/U | ret.h.f.*/T]
//   [p.f.NE/U | ret.h.$/T, ret.h.*/T, ret.h.f.$/T, ret.h.f.*/T]
//   [p.M/U | ret.h.*/T, ret.h.f.*/T]
//   [p.f.$/U | ret.h.f.*/T]
// Submitted facts:
//   N: p.f.g.MUST/T
//   N: p.f.g.MUST/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.MUST/T
//   D: p.f.g.*/T, p.f.*/T, p.f.g.$/T, p.f.h.*/T, p.f.$/T, p.f.h.$/T, p.$/T, p.*/T
//   N: p.f.g.*/FLOW, p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.f.h.*/FLOW, p.*/FLOW
//   D: p.f.g.*/U, p.f.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.MUST/T
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.MUST/T -> N,H=0: ret.h.f.g.MUST/U
// Published qualified DEMAND summaries:
//   p.f.g.*/T -> D,H=0: ret.h.f.NE/U, ret.h.f.g.MUST/U
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.f.NE/U, ret.h.f.M/U, ret.h.f.g.MUST/U, ret.h.$/U, ret.h.f.$/U
//   p.f.g.*/U -> D,H=0: ret.h.f.NE/T, ret.h.f.g.MUST/T
//   p.f.*/U -> D,H=0: ret.h.M/T, ret.h.f.NE/T, ret.h.f.M/T, ret.h.f.g.MUST/T
//   p.f.g.$/T -> D,H=0: ret.h.f.g.MUST/U
//   p.f.h.*/T -> D,H=0: ret.h.$/U, ret.h.M/U, ret.h.f.NE/U, ret.h.f.$/U, ret.h.f.M/U, ret.h.f.g.MUST/U
//   p.f.$/T -> D,H=0: ret.h.f.NE/U, ret.h.f.g.MUST/U
//   p.f.h.$/T -> D,H=0: ret.h.f.NE/U, ret.h.f.g.MUST/U
//   p.$/T -> D,H=0: ret.h.f.g.MUST/U, ret.h.f.NE/U
//   p.*/T -> D,H=0: ret.h.M/U, ret.h.f.NE/U, ret.h.f.M/U, ret.h.f.g.MUST/U
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.MUST/T,N,H=0
void root(Box a) { // Entry marking: T uniformly at a.f.g.MUST.
    Box x = make(a).h; // x.f.g.MUST/U,N,H=0
    Box y = make(x).h; // y.M/T,D,H=0
    Box z = make(y).h; // z.M/U,D,H=0
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-6, backward, field limit 5

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.f.*/U -> D,H=0: p.f.g.M/T, p.f.h.NE/T, p.f.M/T, p.f.h.g.M/T, p.f.h.M/T, p.f.$/T, p.f.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/U -> D,H=0: p.f.g.M/T, p.f.h.NE/T, p.f.M/T, p.f.g.$/T, p.f.h.g.M/T, p.f.h.M/T, p.f.$/T, p.f.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.*/U -> D,H=0: p.f.g.M/T, p.f.h.NE/T, p.f.M/T, p.f.g.$/T, p.f.h.g.M/T, p.f.h.M/T, p.f.$/T, p.f.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D,H=0: p.f.h.NE/T, p.f.h.g.M/T, p.f.NE/T
//   ret.h.*/U -> D,H=0: p.f.h.NE/T, p.f.M/T, p.f.h.g.M/T, p.f.h.M/T, p.f.NE/T, p.M/T
//   ret.h.f.$/U -> D,H=0: p.f.h.NE/T, p.f.h.g.M/T, p.f.NE/T
//   ret.h.f.g.$/T -> D,H=0: p.f.g.M/U, p.f.h.NE/U, p.f.M/U
//   ret.h.f.g.*/T -> D,H=0: p.f.g.M/U, p.f.h.NE/U, p.f.M/U
//   ret.h.f.*/T -> D,H=0: p.f.h.NE/U, p.f.M/U, p.f.g.M/U
//   ret.h.$/T -> D,H=0: p.f.h.NE/U
//   ret.h.*/T -> D,H=0: p.f.h.NE/U, p.f.M/U
//   ret.h.f.$/T -> D,H=0: p.f.h.NE/U
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.f.NE/U | p.f.g.*/T, p.f.*/T, p.f.h.*/T, p.f.$/T, p.f.h.$/T, p.$/T, p.*/T]
//   [ret.h.f.g.M/U | p.f.g.*/T, p.f.*/T, p.f.g.$/T, p.f.h.*/T, p.f.$/T, p.f.h.$/T, p.$/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.f.h.*/T, p.*/T]
//   [ret.h.f.M/U | p.f.*/T, p.f.h.*/T, p.*/T]
//   [ret.h.f.NE/T | p.f.g.*/U, p.f.*/U]
//   [ret.h.f.g.M/T | p.f.g.*/U, p.f.*/U]
//   [ret.h.M/T | p.f.*/U]
//   [ret.h.f.M/T | p.f.*/U]
//   [ret.h.$/U | p.f.h.*/T, p.f.*/T]
//   [ret.h.f.$/U | p.f.h.*/T, p.f.*/T]
// Submitted facts:
//   D: ret.h.M/U, ret.h.f.M/U
//   D: ret.h.f.g.M/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U, ret.h.$/U, ret.h.*/U, ret.h.f.$/U
//   N: ret.h.f.*/FLOW, ret.h.f.g.*/FLOW, ret.h.*/FLOW, ret.h.$/FLOW, ret.h.f.$/FLOW
//   D: ret.h.f.g.$/T, ret.h.f.g.*/T, ret.h.f.*/T, ret.h.$/T, ret.h.*/T, ret.h.f.$/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D,H=0
    Box y = make(x).h; // backward requirements at x: x.f.M/U,D,H=0
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
//   [p.f.g.M/T | ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.h.NE/T | ret.h.$/U, ret.h.*/U, ret.h.f.$/U, ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.M/T | ret.h.*/U, ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.g.$/T | ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.h.g.M/T | ret.h.$/U, ret.h.*/U, ret.h.f.$/U, ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.h.M/T | ret.h.*/U, ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.$/T | ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.h.$/T | ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.$/T | ret.h.f.g.$/U, ret.h.f.g.*/U, ret.h.f.*/U]
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U, ret.h.f.$/U, ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.M/T | ret.h.*/U, ret.h.f.*/U, ret.h.f.g.$/U, ret.h.f.g.*/U]
//   [p.f.g.M/U | ret.h.f.g.$/T, ret.h.f.g.*/T, ret.h.f.*/T]
//   [p.f.h.NE/U | ret.h.f.*/T, ret.h.f.g.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T, ret.h.f.$/T]
//   [p.f.M/U | ret.h.f.*/T, ret.h.f.g.$/T, ret.h.f.g.*/T, ret.h.*/T]
// Submitted facts:
//   N: p.f.g.MUST/T, p.f.g.$/T
//   N: p.f.g.MUST/U, p.f.g.$/U
// Emitted initials:
//   N: p.f.g.MUST/T, p.f.g.$/T
//   D: p.f.g.*/T, p.f.*/T
//   N: p.f.g.*/FLOW, p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW
//   N: p.f.g.MUST/U, p.f.g.$/U
//   D: p.f.g.*/U
// Whole complete keys:
//   p.f.g.$/T
//   p.f.g.$/U
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.MUST/T
//   p.f.g.$/T
//   p.f.g.MUST/U
//   p.f.g.$/U
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.MUST/T -> N,H=0: ret.h.f.g.MUST/U, ret.h.f.g.$/U
//   p.f.g.$/T -> N,H=0: ret.h.f.g.$/U, ret.h.f.g.MUST/U
//   p.f.g.MUST/U -> N,H=0: ret.h.f.g.$/T, ret.h.f.g.MUST/T
//   p.f.g.$/U -> N,H=0: ret.h.f.g.$/T, ret.h.f.g.MUST/T
// Published qualified DEMAND summaries:
//   p.f.g.*/T -> D,H=0: ret.h.f.NE/U, ret.h.f.g.MUST/U, ret.h.f.g.$/U
//   p.f.g.MUST/T -> D,H=0: ret.h.f.NE/U
//   p.f.*/T -> D,H=0: ret.h.M/U, ret.h.f.NE/U, ret.h.f.M/U, ret.h.f.g.MUST/U, ret.h.f.g.$/U, ret.h.f.g.M/U
//   p.f.g.*/U -> D,H=0: ret.h.f.g.MUST/T, ret.h.f.g.$/T, ret.h.f.NE/T
//   p.f.g.$/U -> D,H=0: ret.h.f.NE/T
//   p.f.g.$/T -> D,H=0: ret.h.f.NE/U
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.MUST/T,N,H=0
void root(Box a) { // Entry marking: T uniformly at a.f.g.MUST.
    Box x = make(a).h; // x.f.g.$/U,N,H=0; x.f.g.MUST/U,N,H=0
    Box y = make(x).h; // y.f.g.$/T,N,H=0; y.f.g.MUST/T,N,H=0
    Box z = make(y).h; // z.f.g.$/U,N,H=0; z.f.g.MUST/U,N,H=0
    // Observe CM(z.M,U).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```

### Run-8, backward, field limit 7

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries: none
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.f.NE/U | p.f.g.*/T, p.f.g.M/T, p.f.*/T, p.f.g.$/T]
//   [ret.h.f.g.M/U | p.f.g.*/T, p.f.*/T]
//   [ret.h.f.g.$/U | p.f.g.*/T, p.f.*/T]
//   [ret.h.M/U | p.f.*/T]
//   [ret.h.f.M/U | p.f.*/T]
//   [ret.h.f.g.M/T | p.f.g.*/U]
//   [ret.h.f.g.$/T | p.f.g.*/U]
//   [ret.h.f.NE/T | p.f.g.*/U, p.f.g.$/U]
// Submitted facts: none
// Emitted initials: none
// Whole complete keys:
//   p.f.g.$/T
//   p.f.g.$/U
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

### Run-9, forward, field limit 8

```java
// Demand [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
// Whole complete keys:
//   p.f.g.$/T
//   p.f.g.$/U
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
Box make(Box p) {
    Box r = new Box();
    // For each input mark m in {T,U}, assign the other mark:
    // CM(p.f.h.g.M,m) => assign other(m) to r.h.MUST.
    // CM(p.M,m)       => assign other(m) to r.h.f.g.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries: none
```

```java
// Demand control: inactive
// Submitted ZERO / emitted ZERO: none
// Entry DATA: none
void root(Box a) { // Entry marking: T uniformly at a.f.g.MUST.
    Box x = make(a).h; // none
    Box y = make(x).h; // none
    Box z = make(y).h; // none
    // Observe CM(z.M,U).
}
// Published: no new DemandTarget.
// NORMAL observation: retained NormalTarget(id).
```


## Uncapped suffix

Protected-input reference: NORMAL observation at run-5; quiet from run-6;
the empty forward frontier is confirmed at run-7.
Uniform reference: NORMAL observation at run-7; quiet from run-8;
the empty forward frontier is confirmed at run-9.
The cold proof modules check all within-run fixed points and prove
that every later uncapped state stays quiet. The natural engine can stop earlier
than the diagnostic histories shown here; neither result uses a hard limit.

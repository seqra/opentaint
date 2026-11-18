# Protected relevant returns: complete fact trace

17 November 2026. Synthetic data-flow reachability. Production unchanged.
[Counterexample, exact recurrence and scope](bidirectional-relevant-protected-return-nontermination-20261117.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
E/mx are empty. H=1 is protected; H=0 is plain. Grouped rows abbreviate separate scalar members.
The shared make owner aggregates all three ordinary call offers. Each call is followed
by an ordinary field read of h. No configured pass or cleaner is used.
Query bindings list AP/layer; literal H is shown on output values and caller packets.
The model uses the same query key as before. Every newly generated output is protected,
so the plain-reply pruning guard fails regardless of the original packet protection.
Helper submissions include the reverse h read during backward runs. Root annotations
use only code variables a/x/y/z. All current mechanisms and field caps stay enabled.
The root controller explicitly models ZERO/Target permissions and accumulates Targets.
Forward: demand/submitted/initials above the body; summaries below.
Backward: summaries above; demand/submitted/initials below.
The full cold prefix through run-10 is followed by a proved uncapped two-state cycle.

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
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
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
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
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
//   N: p.f.g.$/T, p.h.MUST/T
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T
//   D: p.f.*/T, p.h.*/T, p.$/T, p.*/T, p.f.$/T
//   N: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW, p.*/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=1: ret.h.h.MUST/T
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.$/T
//   p.h.*/T -> D,H=1: ret.h.h.MUST/T
//   p.$/T -> D,H=1: ret.h.h.MUST/T
//   p.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T
//   p.f.$/T -> D,H=1: ret.h.h.MUST/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/T,N,H=1; x.M/T,D,H=1
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
//   ret.h.$/T -> D,H=1: p.f.g.NE/T, p.f.NE/T
//   ret.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.h.$/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.f.*/T -> D,H=1: p.f.g.NE/T, p.f.NE/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/T | p.f.*/T, p.*/T]
//   [ret.h.h.M/T | p.f.*/T, p.h.*/T, p.$/T, p.*/T, p.f.$/T]
//   [ret.h.$/T | p.f.*/T]
// Submitted facts:
//   D: ret.h.M/T, ret.h.f.g.$/T
// Emitted initials:
//   D: ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.f.g.$/T,D,H=0; a.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.f.g.$/T,D,H=0; x.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.f.g.$/T,D,H=0; y.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

### Run-5, forward, field limit 4

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T]
//   [p.f.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.M/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T]
//   [p.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.$/T | ret.h.h.$/T, ret.h.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
//   p.h.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.h.MUST/T -> N,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=1: ret.h.h.$/T, ret.h.h.MUST/T
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.$/T, ret.h.f.M/T
//   p.h.*/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.*/T -> D,H=1: ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.f.M/T
//   p.f.$/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.$/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.h.$/T -> D,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/T -> D,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/T,N,H=1; x.h.$/T,N,H=1; x.M/T,D,H=1
    Box y = make(x).h; // y.h.$/T,N,H=1; y.h.MUST/T,N,H=1; y.M/T,D,H=1
    Box z = make(y).h; // z.h.$/T,N,H=1; z.h.MUST/T,N,H=1; z.M/T,D,H=1
    // Observe CM(z.M,T).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-6, backward, field limit 5

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.NE/T
//   ret.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.NE/T, p.M/T
//   ret.h.h.$/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.$/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T
//   ret.h.f.*/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.NE/T
//   ret.h.f.g.$/T -> D,H=1: p.f.g.g.M/T, p.f.g.NE/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/T | p.f.*/T, p.f.g.*/T, p.*/T]
//   [ret.h.h.M/T | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/T | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/T | p.f.g.*/T, p.f.*/T]
//   [ret.h.f.M/T | p.f.g.*/T, p.f.*/T]
// Submitted facts:
//   D: ret.h.M/T, ret.h.f.g.$/T, ret.h.h.M/T
// Emitted initials:
//   D: ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.$/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.f.g.$/T,D,H=0; a.h.M/T,D,H=0; a.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.f.g.$/T,D,H=0; x.h.M/T,D,H=0; x.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.f.g.$/T,D,H=0; y.h.M/T,D,H=0; y.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

### Run-7, forward, field limit 6

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T]
//   [p.f.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.M/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.g.M/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T]
//   [p.f.g.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T]
//   [p.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.f.g.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
//   p.h.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.h.MUST/T -> N,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=1: ret.h.h.$/T, ret.h.h.MUST/T
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.$/T, ret.h.f.M/T
//   p.h.*/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.*/T -> D,H=1: ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.f.$/T, ret.h.f.M/T, ret.h.f.g.$/T
//   p.f.g.g.$/T -> D,H=1: ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.f.MUST/T, ret.h.f.g.$/T
//   p.f.g.g.*/T -> D,H=1: ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.f.MUST/T, ret.h.f.g.$/T
//   p.f.$/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.$/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.h.$/T -> D,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/T -> D,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/T,N,H=1; x.h.$/T,N,H=1; x.M/T,D,H=1
    Box y = make(x).h; // y.h.$/T,N,H=1; y.h.MUST/T,N,H=1; y.M/T,D,H=1
    Box z = make(y).h; // z.h.$/T,N,H=1; z.h.MUST/T,N,H=1; z.M/T,D,H=1
    // Observe CM(z.M,T).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-8, backward, field limit 7

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.$/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T
//   ret.h.f.*/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.f.g.$/T -> D,H=1: p.f.g.g.M/T, p.f.g.g.$/T, p.f.g.NE/T
//   ret.h.f.g.*/T -> D,H=1: p.f.g.g.M/T, p.f.g.g.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/T | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.h.M/T | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/T | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/T | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
//   [ret.h.f.$/T | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T]
//   [ret.h.f.M/T | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
//   [ret.h.f.g.$/T | p.f.g.g.$/T, p.f.g.g.*/T, p.f.g.*/T]
// Submitted facts:
//   D: ret.h.M/T, ret.h.f.g.$/T, ret.h.h.M/T
// Emitted initials:
//   D: ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T, ret.h.f.g.*/T
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.f.g.*/FLOW, ret.h.$/FLOW, ret.h.f.$/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.f.g.$/T,D,H=0; a.h.M/T,D,H=0; a.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.f.g.$/T,D,H=0; x.h.M/T,D,H=0; x.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.f.g.$/T,D,H=0; y.h.M/T,D,H=0; y.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

### Run-9, forward, field limit 8

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T]
//   [p.f.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.M/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.g.M/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T, ret.h.f.g.*/T]
//   [p.f.g.g.$/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T, ret.h.f.g.*/T]
//   [p.f.g.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.g.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.$/T | ret.h.h.$/T, ret.h.h.*/T]
//   [p.f.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T]
//   [p.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.f.g.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys:
//   p.f.g.$/T
//   p.h.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.h.MUST/T -> N,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N,H=1: ret.h.h.$/T, ret.h.h.MUST/T
// Published qualified DEMAND summaries:
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.$/T, ret.h.f.M/T
//   p.h.*/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.*/T -> D,H=1: ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.f.$/T, ret.h.f.M/T, ret.h.f.g.$/T
//   p.f.g.g.$/T -> D,H=1: ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.f.MUST/T, ret.h.f.g.$/T, ret.h.f.g.MUST/T
//   p.f.g.g.*/T -> D,H=1: ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.f.MUST/T, ret.h.f.g.$/T, ret.h.f.g.MUST/T
//   p.f.$/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.$/T -> D,H=1: ret.h.h.MUST/T, ret.h.h.$/T
//   p.h.$/T -> D,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/T -> D,H=1: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/T,N,H=1; x.h.$/T,N,H=1; x.M/T,D,H=1
    Box y = make(x).h; // y.h.$/T,N,H=1; y.h.MUST/T,N,H=1; y.M/T,D,H=1
    Box z = make(y).h; // z.h.$/T,N,H=1; z.h.MUST/T,N,H=1; z.M/T,D,H=1
    // Observe CM(z.M,T).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-10, backward, field limit 9

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.$/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T
//   ret.h.f.*/T -> D,H=1: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.f.g.$/T -> D,H=1: p.f.g.g.M/T, p.f.g.g.$/T, p.f.g.NE/T
//   ret.h.f.g.*/T -> D,H=1: p.f.g.g.M/T, p.f.g.g.$/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/T | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.h.M/T | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.h.$/T | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/T | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
//   [ret.h.f.$/T | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T]
//   [ret.h.f.M/T | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
//   [ret.h.f.g.$/T | p.f.g.g.$/T, p.f.g.g.*/T, p.f.g.*/T]
//   [ret.h.f.g.M/T | p.f.g.g.$/T, p.f.g.g.*/T]
// Submitted facts:
//   D: ret.h.M/T, ret.h.f.g.$/T, ret.h.h.M/T
// Emitted initials:
//   D: ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.*/T, ret.h.f.g.$/T, ret.h.f.g.*/T
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.f.g.*/FLOW, ret.h.$/FLOW, ret.h.f.$/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.f.g.$/T,D,H=0; a.h.M/T,D,H=0; a.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.f.g.$/T,D,H=0; x.h.M/T,D,H=0; x.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.f.g.$/T,D,H=0; y.h.M/T,D,H=0; y.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

## Uncapped repeated pair

For every n >= 0, history(2*n+9) is the complete run-9 state,
and history(2*n+10) is the complete run-10 state.
Helper DATA demand counts remain 41/47; six NORMAL records remain retained.
Every forward state has a root DemandTarget; every backward state renews entry permission.
The NORMAL observation stays retained from run-5. It does not cancel DemandTarget.
Within-run fixed points are also checked: this is not a fuel timeout.

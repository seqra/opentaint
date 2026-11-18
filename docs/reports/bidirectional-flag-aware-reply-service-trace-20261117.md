# Within-flag NORMAL service: repaired fact trace

17 November 2026. Synthetic data-flow reachability. Production unchanged.
[Selected repair and validation](../design/bidirectional-flag-aware-reply-service-20261117.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
E/mx are empty. H=1 is protected; H=0 is plain. Grouped rows abbreviate separate scalar members.
The shared make owner aggregates all three ordinary call offers. Each call is followed
by an ordinary field read of h. No configured pass or cleaner is used.
Query bindings list AP/layer; literal H is shown on output values and caller packets.
The model uses the same query key as before. Every newly generated output is protected,
and only actual same-flag NORMAL service can select a protected coarse reply.
Helper submissions include the reverse h read during backward runs. Root annotations
use only code variables a/x/y/z. All current mechanisms and field caps stay enabled.
The root controller explicitly models ZERO/Target permissions and accumulates Targets.
Forward: demand/submitted/initials above the body; summaries below.
Backward: summaries above; demand/submitted/initials below.
The reference stops naturally at run-5; all runs from run-6 are quiet.

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
//   D: p.h.MUST/T
// Emitted initials:
//   N: p.f.g.$/T
//   D: p.f.*/T, p.h.*/T
//   N: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW
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
//   p.f.*/T -> D,H=1: ret.h.M/T, ret.h.h.MUST/T
//   p.h.*/T -> D,H=1: ret.h.h.MUST/T
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/T,N,H=1
    Box y = make(x).h; // y.h.MUST/T,D,H=1
    Box z = make(y).h; // z.h.MUST/T,D,H=1
    // Observe CM(z.M,T).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/T -> D,H=1: p.f.g.NE/T
//   ret.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T
//   ret.h.h.$/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T
//   ret.h.h.*/T -> D,H=1: p.f.g.NE/T, p.f.M/T, p.h.M/T
//   ret.h.f.*/T -> D,H=1: p.f.g.NE/T
//   ret.h.f.$/T -> D,H=1: p.f.g.NE/T
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.   // H=1
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/T | p.f.*/T]
//   [ret.h.h.M/T | p.f.*/T, p.h.*/T]
// Submitted facts:
//   D: ret.h.M/T, ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.M/T
// Emitted initials:
//   D: ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T, ret.h.f.$/T
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW
// Whole complete keys: none
// Mark-scoped complete keys: none
// Current-owner full NORMAL closure keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.f.g.$/T,D,H=0; a.f.M/T,D,H=1; a.h.M/T,D,H=1
    Box y = make(x).h; // backward requirements at x: x.f.g.$/T,D,H=0; x.f.M/T,D,H=1; x.h.M/T,D,H=1
    Box z = make(y).h; // backward requirements at y: y.f.g.$/T,D,H=0; y.f.M/T,D,H=1; y.h.M/T,D,H=1
    // Backward observation input at z: z.M/T,D,H=0
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/T,D,H=0
```

### Run-5, forward, field limit 4

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.h.$/T, ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.*/T, ret.h.f.$/T]
//   [p.f.M/T | ret.h.*/T, ret.h.h.$/T, ret.h.h.*/T]
//   [p.h.M/T | ret.h.h.$/T, ret.h.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW
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
// Published qualified DEMAND summaries: none
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N,H=0
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/T,N,H=1; x.h.$/T,N,H=1
    Box y = make(x).h; // y.h.$/T,N,H=1; y.h.MUST/T,N,H=1
    Box z = make(y).h; // z.h.$/T,N,H=1; z.h.MUST/T,N,H=1
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
    // CM(p.M,T)       => assign T to r.h.h.MUST. // H=1
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
NORMAL observation remains retained from run-5. No DATA or Target demand revives.
The earlier run-3 DemandTarget was not canceled. Within-run fixed points are checked.

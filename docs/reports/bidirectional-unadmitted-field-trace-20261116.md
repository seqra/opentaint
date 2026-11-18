# Same-mark disjoint-return cycle: complete fact trace

Historical before-change trace. The
[reply-scoped repair](../design/bidirectional-reply-scoped-point-service-20261116.md)
now stops this example at run-5. See the
[updated trace](bidirectional-reply-scoped-point-service-trace-20261116.md).
The uncapped run-11/run-12 recurrence below remains the checked old result.

16 November 2026. Synthetic data-flow reachability. Production unchanged.
[Counterexample and uncapped proof](bidirectional-unadmitted-field-nontermination-20261116.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
All H are plain; E/mx are empty. Grouped pairs abbreviate separate scalar rows.
The shared make owner aggregates all three ordinary call offers. Each call is followed
by a real field read of h. These reads are instructions, not configured pass rules.
Helper submitted facts include the reverse h read in backward runs. Root lines show
the packets after each forward read, or before each reverse read, in code variable names.
All eligible C2 children, current C5 results and saved NORMAL service remain enabled.
The fixed reference controller explicitly models root ZERO/Target permissions.
For forward runs inputs are above each body and outputs below. Backward placement reverses this.
The full cold prefix through run-12 is followed by a proved two-state uncapped suffix.

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
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   p.*/T -> D: ret.h.M/U, ret.h.NE/U, ret.k.MUST/U
//   p.*/U -> D: ret.h.M/T, ret.h.NE/T, ret.k.MUST/T
```

```java
// Demand control: unrestricted run-1
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.NE/T,D
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.M/U,D
    Box y = make(x).h; // y.M/T,D
    Box z = make(y).h; // z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-2, backward, field limit 1

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D: p.f.NE/T
//   ret.h.*/U -> D: p.f.NE/T, p.M/T
//   ret.h.$/T -> D: p.f.NE/U
//   ret.h.*/T -> D: p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Demand [entry | paired output]:
//   [ret.h.M/U | p.*/T]
//   [ret.h.NE/U | p.*/T]
//   [ret.k.M/U | p.*/T]
//   [ret.h.M/T | p.*/U]
//   [ret.h.NE/T | p.*/U]
//   [ret.k.M/T | p.*/U]
// Submitted facts:
//   D: ret.h.M/U
//   D: ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U
//   N: ret.h.*/FLOW
//   D: ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D
    Box y = make(x).h; // backward requirements at x: x.M/U,D
    Box z = make(y).h; // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
```

### Run-3, forward, field limit 2

```java
// Demand [entry | paired output]:
//   [p.f.NE/T | ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.h.*/U]
//   [p.f.NE/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.*/T]
// Submitted facts:
//   N: p.f.g.$/T
//   N: p.h.MUST/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T
//   D: p.f.*/T, p.$/T, p.*/T, p.f.$/T
//   N: p.f.*/FLOW, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW, p.*/FLOW
//   D: p.h.*/U, p.f.*/U, p.$/U, p.*/U, p.f.$/U
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.$/U
//   p.h.*/U -> D: ret.h.h.MUST/T
//   p.f.*/U -> D: ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T
//   p.$/U -> D: ret.h.h.MUST/T
//   p.*/U -> D: ret.h.M/T, ret.h.h.MUST/T
//   p.f.$/U -> D: ret.h.h.MUST/T
//   p.$/T -> D: ret.h.h.MUST/U
//   p.*/T -> D: ret.h.M/U, ret.h.h.MUST/U
//   p.f.$/T -> D: ret.h.h.MUST/U
// Raw ret.k.MUST/T or U is outside every paired h output.
// The missing service has the SAME mark as ret.h.h; full-mark completion also fails.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N; x.M/U,D
    Box y = make(x).h; // y.M/T,D
    Box z = make(y).h; // z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

### Run-4, backward, field limit 3

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.NE/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.$/T, p.f.NE/T, p.M/T, p.f.$/T
//   ret.h.f.*/T -> D: p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D: p.h.M/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.h.h.*/T -> D: p.h.M/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U, p.f.$/U
//   ret.h.$/T -> D: p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D: p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
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
//   D: ret.h.M/U
//   D: ret.h.f.g.$/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW
//   D: ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D
    Box y = make(x).h; // backward requirements at x: x.M/U,D
    Box z = make(y).h; // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
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
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N: ret.h.h.MUST/U, ret.h.h.$/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.*/U -> D: ret.h.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
//   p.f.*/U -> D: ret.h.f.M/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.$/T
//   p.h.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D: ret.h.h.MUST/T, ret.h.h.$/T
//   p.f.g.$/U -> D: ret.h.h.MUST/T, ret.h.h.$/T
//   p.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D: ret.h.M/T, ret.h.h.MUST/T, ret.h.h.$/T, ret.h.h.M/T
//   p.h.*/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.*/T -> D: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Raw ret.k.MUST/T or U is outside every paired h output.
// The missing service has the SAME mark as ret.h.h; full-mark completion also fails.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x).h; // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y).h; // z.h.MUST/U,N; z.h.$/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-6, backward, field limit 5

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.NE/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D: p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D: p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.f.g.$/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.f.g.$/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D: p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.$/T -> D: p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D: p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
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
//   D: ret.h.M/U, ret.h.h.M/U
//   D: ret.h.f.g.$/T, ret.h.h.$/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW
//   D: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D
    Box y = make(x).h; // backward requirements at x: x.M/U,D
    Box z = make(y).h; // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
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
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N: ret.h.h.$/U, ret.h.h.MUST/U
//   p.h.MUST/T -> N: ret.h.h.$/U, ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.*/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.$/U -> D: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T
//   p.f.g.g.*/U -> D: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.$/T, ret.h.MUST/T, ret.h.h.MUST/T
//   p.f.g.*/U -> D: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.$/T, ret.h.f.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.M/T, ret.h.$/T
//   p.f.*/U -> D: ret.h.f.M/T, ret.h.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.M/T, ret.h.$/T
//   p.h.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.g.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D: ret.h.h.$/T, ret.h.M/T, ret.h.h.MUST/T, ret.h.h.M/T
//   p.f.g.*/T -> D: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.g.g.$/T -> D: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.*/T -> D: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Raw ret.k.MUST/T or U is outside every paired h output.
// The missing service has the SAME mark as ret.h.h; full-mark completion also fails.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x).h; // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y).h; // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-8, backward, field limit 7

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.g.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.h.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
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
//   D: ret.h.M/U, ret.h.h.M/U
//   D: ret.h.f.g.$/T, ret.h.h.M/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.g.*/FLOW
//   D: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D
    Box y = make(x).h; // backward requirements at x: x.M/U,D
    Box z = make(y).h; // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
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
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N: ret.h.h.$/U, ret.h.h.MUST/U
//   p.h.MUST/T -> N: ret.h.h.$/U, ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.*/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.$/U -> D: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.g.*/U -> D: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.*/U -> D: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.M/T, ret.h.$/T
//   p.f.*/U -> D: ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T, ret.h.$/T
//   p.h.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.g.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D: ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T
//   p.f.g.*/T -> D: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.g.g.$/T -> D: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.*/T -> D: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Raw ret.k.MUST/T or U is outside every paired h output.
// The missing service has the SAME mark as ret.h.h; full-mark completion also fails.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x).h; // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y).h; // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-10, backward, field limit 9

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.g.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.h.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
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
//   D: ret.h.M/U, ret.h.h.M/U
//   D: ret.h.f.g.$/T, ret.h.h.M/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.g.*/FLOW
//   D: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D
    Box y = make(x).h; // backward requirements at x: x.M/U,D
    Box z = make(y).h; // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
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
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.$/T, p.h.MUST/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Whole complete keys: none
// Mark-scoped complete keys: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
    return r;
}
// Admitted current NORMAL summaries:
//   p.f.g.$/T -> N: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.MUST/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/U -> N: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.$/T -> N: ret.h.h.$/U, ret.h.h.MUST/U
//   p.h.MUST/T -> N: ret.h.h.$/U, ret.h.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U, ret.h.$/U
//   p.h.*/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.h.*/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.$/U -> D: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.g.*/U -> D: ret.h.f.g.$/T, ret.h.f.MUST/T, ret.h.h.$/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.f.g.MUST/T, ret.h.$/T, ret.h.MUST/T
//   p.f.g.*/U -> D: ret.h.f.g.$/T, ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.f.$/T, ret.h.M/T, ret.h.$/T
//   p.f.*/U -> D: ret.h.f.M/T, ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T, ret.h.$/T
//   p.h.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.g.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.f.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.$/U -> D: ret.h.h.$/T, ret.h.h.MUST/T
//   p.*/U -> D: ret.h.h.$/T, ret.h.h.M/T, ret.h.h.MUST/T, ret.h.M/T
//   p.f.g.*/T -> D: ret.h.$/U, ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
//   p.f.g.g.$/T -> D: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.g.*/T -> D: ret.h.$/U, ret.h.MUST/U, ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.f.g.$/T -> D: ret.h.h.MUST/U, ret.h.h.$/U
//   p.h.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.$/T -> D: ret.h.h.$/U, ret.h.h.MUST/U
//   p.*/T -> D: ret.h.M/U, ret.h.h.MUST/U, ret.h.h.$/U, ret.h.h.M/U
// Raw ret.k.MUST/T or U is outside every paired h output.
// The missing service has the SAME mark as ret.h.h; full-mark completion also fails.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a).h; // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x).h; // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y).h; // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

### Run-12, backward, field limit 11

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.f.g.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.f.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.h.f.g.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.h.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.h.MUST.
    // CM(p.M,T)       => assign U to r.h.h.MUST.
    // CM(p.M,T)       => assign U to r.k.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.h.MUST.
    // CM(p.M,U)       => assign T to r.h.h.MUST.
    // CM(p.M,U)       => assign T to r.k.MUST.
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
//   D: ret.h.M/U, ret.h.h.M/U
//   D: ret.h.f.g.$/T, ret.h.h.M/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U, ret.h.h.$/U, ret.h.h.*/U
//   N: ret.h.*/FLOW, ret.h.h.*/FLOW, ret.h.f.$/FLOW, ret.h.f.*/FLOW, ret.h.$/FLOW, ret.h.f.g.*/FLOW
//   D: ret.h.f.g.$/T, ret.h.f.*/T, ret.h.h.$/T, ret.h.h.*/T, ret.h.f.$/T, ret.h.f.g.*/T, ret.h.$/T, ret.h.*/T
// Whole complete keys: none
// Mark-scoped complete keys: none
```

```java
// Published control summary: ZERO -> DemandTarget,D; entry-marking permission renewed.
// NormalTarget is ignored backward; the prior NORMAL report remains retained.
void root(Box a) {
    Box x = make(a).h; // backward requirements at a: a.M/T,D
    Box y = make(x).h; // backward requirements at x: x.M/U,D
    Box z = make(y).h; // backward requirements at y: y.M/T,D
    // Backward observation input at z: z.M/U,D
}
// Demand control: [Target | ZERO]
// Submitted ZERO / emitted ZERO: active
// Backward observation input at z: z.M/U,D
```

## Every later iteration

For every n >= 0, the complete run-(11+2n) state equals run-11, and the complete
run-(12+2n) state equals run-12. Both have nonempty demand; forward runs emit
DemandTarget and backward runs renew the entry-marking permission. This includes
saved service, both completion caches, all actual submissions and C5 results.
The equality holds at arbitrary later budgets >= 8, not merely up to run-11 or run-31.

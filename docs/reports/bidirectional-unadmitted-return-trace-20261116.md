# Unadmitted NORMAL return: complete counterexample trace

16 November 2026. Synthetic data-flow reachability. Production is unchanged.
[Contract, root cause, scope and uncapped proof](bidirectional-unadmitted-return-nontermination-20261116.md).

`$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
All H are plain and all E/mx are empty. Each `[entry | output1, output2]`
lists separate complete paired demand rows. Summary lines with multiple
conclusions also abbreviate separate scalar rows. No declared relation is assumed.
The make owner aggregates all three actual submissions. NORMAL lines are current
post-C5 candidates; saved NORMAL rows also replay normally. Completed keys are shown.
For forward iterations, demand/submitted/initials appear above the body, summaries below.
Backward iterations reverse this placement. The fixed reference controller explicitly
models root ZERO/Target permissions. Aliases/JVM front-end expansion are not modeled.

## Run-1, forward, field limit 1

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
// Completed exact-query keys: none
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
// Submitted ZERO; emitted ZERO initial.
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

## Run-2, backward, field limit 1

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
// Completed exact-query keys: none
```

```java
// Published: ZERO -> DemandTarget,D; source permission renewed.
void root(Box a) {
    // Entry marking check inputs: a.M/T,D; a.s.M/V,D
    Box x = make(a); // requires a.M/T,D; a.s.M/V,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D; y.s.M/V,D
    // Backward observation input: z.M/U,D
}
// Submitted ZERO at normal exit; emitted ZERO initial.
// Demand control [Target | ZERO]; NormalTarget is ignored backward.
```

## Run-3, forward, field limit 2

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
// Completed exact-query keys:
//   p.h.$/U
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
// Unadmitted raw NORMAL return: p.f.g.$/T -> ret.k.MUST/V.
// The same fine T query thus has no complete admitted NORMAL service.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO; emitted ZERO initial.
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

## Run-4, backward, field limit 3

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
// Completed exact-query keys:
//   p.h.$/U
```

```java
// Published: ZERO -> DemandTarget,D; source permission renewed.
void root(Box a) {
    // Entry marking check inputs: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation input: z.M/U,D
}
// Submitted ZERO at normal exit; emitted ZERO initial.
// Demand control [Target | ZERO]; NormalTarget is ignored backward.
```

## Run-5, forward, field limit 4

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
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Completed exact-query keys:
//   p.h.$/U
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
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.*/U -> D: ret.f.M/T, ret.h.$/T, ret.$/T, ret.M/T, ret.h.MUST/T, ret.h.M/T
//   p.f.*/U -> D: ret.f.M/T, ret.h.$/T, ret.M/T, ret.h.MUST/T, ret.h.M/T, ret.$/T
//   p.h.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.g.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.*/U -> D: ret.h.$/T, ret.M/T, ret.h.MUST/T, ret.h.M/T
//   p.f.g.*/T -> D: ret.$/U, ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.h.$/T -> D: ret.h.MUST/U, ret.h.$/U
// Unadmitted raw NORMAL return: p.f.g.$/T -> ret.k.MUST/V.
// The same fine T query thus has no complete admitted NORMAL service.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO; emitted ZERO initial.
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y); // z.h.MUST/U,N; z.h.$/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

## Run-6, backward, field limit 5

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.$/T, p.f.NE/T, p.M/T, p.h.$/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.$/T, p.f.g.$/T, p.$/T, p.f.NE/T, p.M/T, p.h.$/T
//   ret.f.g.$/T -> D: p.f.g.g.M/U, p.f.g.NE/U
//   ret.f.*/T -> D: p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.f.g.$/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.f.g.$/U, p.$/U, p.f.NE/U, p.M/U
//   ret.f.$/T -> D: p.f.g.g.M/U, p.f.g.NE/U
//   ret.$/T -> D: p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
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
//   [ret.M/U | p.f.*/T, p.f.g.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T, p.h.$/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.$/T, p.f.g.$/T, p.$/T, p.*/T, p.h.$/T]
//   [ret.h.$/T | p.h.*/U, p.h.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.f.g.$/U, p.$/U, p.*/U]
//   [ret.h.M/T | p.h.*/U, p.h.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.f.g.$/U, p.$/U, p.*/U]
//   [ret.f.M/T | p.f.g.*/U, p.f.*/U]
//   [ret.$/T | p.f.g.*/U, p.f.*/U]
//   [ret.M/T | p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.$/U | p.f.g.*/T, p.f.*/T]
// Submitted facts:
//   D: ret.M/U, ret.h.M/U
//   D: ret.f.g.$/T, ret.h.M/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.$/FLOW, ret.f.*/FLOW, ret.$/FLOW
//   D: ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.$/T, ret.*/T
// Completed exact-query keys:
//   p.h.$/U
```

```java
// Published: ZERO -> DemandTarget,D; source permission renewed.
void root(Box a) {
    // Entry marking check inputs: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation input: z.M/U,D
}
// Submitted ZERO at normal exit; emitted ZERO initial.
// Demand control [Target | ZERO]; NormalTarget is ignored backward.
```

## Run-7, forward, field limit 6

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.h.M/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.g.M/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.g.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.$/T | ret.h.$/U, ret.h.*/U]
//   [p.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.h.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.g.M/U | ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.$/T, ret.*/T]
//   [p.f.g.NE/U | ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.$/T, ret.*/T]
//   [p.f.NE/U | ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T]
//   [p.h.M/U | ret.h.$/T, ret.h.*/T]
//   [p.h.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.g.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
//   [p.f.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
//   [p.f.g.$/U | ret.h.$/T, ret.h.*/T]
//   [p.$/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Completed exact-query keys:
//   p.h.$/U
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
//   p.h.MUST/T -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.$/T -> N: ret.h.$/U, ret.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.g.$/U -> D: ret.f.g.$/T, ret.f.MUST/T, ret.h.$/T, ret.h.MUST/T, ret.f.$/T, ret.$/T, ret.MUST/T
//   p.f.g.g.*/U -> D: ret.f.g.$/T, ret.f.MUST/T, ret.h.$/T, ret.h.MUST/T, ret.f.$/T, ret.$/T, ret.MUST/T
//   p.f.g.*/U -> D: ret.f.g.$/T, ret.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.f.$/T, ret.M/T, ret.$/T
//   p.f.*/U -> D: ret.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.M/T, ret.$/T
//   p.h.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.g.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.*/U -> D: ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.M/T
//   p.f.g.*/T -> D: ret.$/U, ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.f.g.g.$/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.g.g.*/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
// Unadmitted raw NORMAL return: p.f.g.$/T -> ret.k.MUST/V.
// The same fine T query thus has no complete admitted NORMAL service.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO; emitted ZERO initial.
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y); // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

## Run-8, backward, field limit 7

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.f.g.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.f.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.f.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.f.g.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
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
//   [ret.M/U | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.M/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.f.g.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.f.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.f.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.$/U | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
// Submitted facts:
//   D: ret.M/U, ret.h.M/U
//   D: ret.f.g.$/T, ret.h.M/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.$/FLOW, ret.f.*/FLOW, ret.$/FLOW, ret.f.g.*/FLOW
//   D: ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.f.g.*/T, ret.$/T, ret.*/T
// Completed exact-query keys:
//   p.h.$/U
```

```java
// Published: ZERO -> DemandTarget,D; source permission renewed.
void root(Box a) {
    // Entry marking check inputs: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation input: z.M/U,D
}
// Submitted ZERO at normal exit; emitted ZERO initial.
// Demand control [Target | ZERO]; NormalTarget is ignored backward.
```

## Run-9, forward, field limit 8

```java
// Demand [entry | paired output]:
//   [p.f.g.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.h.M/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.g.M/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.g.g.$/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.g.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.g.$/T | ret.h.$/U, ret.h.*/U]
//   [p.h.$/T | ret.h.$/U, ret.h.*/U]
//   [p.$/T | ret.h.$/U, ret.h.*/U]
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.g.g.$/U | ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.f.g.*/T, ret.$/T, ret.*/T]
//   [p.f.g.g.M/U | ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.f.g.*/T, ret.$/T, ret.*/T]
//   [p.f.g.NE/U | ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.$/T, ret.*/T]
//   [p.f.NE/U | ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.$/T, ret.*/T]
//   [p.h.M/U | ret.h.$/T, ret.h.*/T]
//   [p.h.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.g.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.g.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
//   [p.f.$/U | ret.h.$/T, ret.h.*/T]
//   [p.f.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
//   [p.$/U | ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.h.$/T, ret.h.*/T, ret.*/T]
// Submitted facts:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.M/U
//   D: p.M/T
// Emitted initials:
//   N: p.f.g.$/T, p.h.MUST/T, p.h.$/T
//   N: p.f.$/FLOW, p.f.*/FLOW, p.$/FLOW, p.h.*/FLOW, p.f.g.g.*/FLOW, p.f.g.*/FLOW, p.*/FLOW
//   D: p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T
//   N: p.h.MUST/U, p.h.$/U
//   D: p.h.*/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.f.g.$/U, p.h.$/U, p.f.$/U, p.$/U, p.*/U
// Completed exact-query keys:
//   p.h.$/U
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
//   p.h.MUST/T -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.$/T -> N: ret.h.$/U, ret.h.MUST/U
// Published qualified DEMAND summaries:
//   p.f.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U, ret.$/U
//   p.h.*/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.g.$/U -> D: ret.f.g.$/T, ret.f.MUST/T, ret.h.$/T, ret.h.MUST/T, ret.f.$/T, ret.f.g.MUST/T, ret.$/T, ret.MUST/T
//   p.f.g.g.*/U -> D: ret.f.g.$/T, ret.f.MUST/T, ret.h.$/T, ret.h.MUST/T, ret.f.$/T, ret.f.g.MUST/T, ret.$/T, ret.MUST/T
//   p.f.g.*/U -> D: ret.f.g.$/T, ret.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.f.$/T, ret.M/T, ret.$/T
//   p.f.*/U -> D: ret.f.M/T, ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.M/T, ret.$/T
//   p.h.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.g.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.f.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.$/U -> D: ret.h.$/T, ret.h.MUST/T
//   p.*/U -> D: ret.h.$/T, ret.h.M/T, ret.h.MUST/T, ret.M/T
//   p.f.g.*/T -> D: ret.$/U, ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
//   p.f.g.g.$/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.g.g.*/T -> D: ret.$/U, ret.MUST/U, ret.h.MUST/U, ret.h.$/U
//   p.f.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.f.g.$/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.$/T -> D: ret.h.$/U, ret.h.MUST/U
//   p.*/T -> D: ret.M/U, ret.h.MUST/U, ret.h.$/U, ret.h.M/U
// Unadmitted raw NORMAL return: p.f.g.$/T -> ret.k.MUST/V.
// The same fine T query thus has no complete admitted NORMAL service.
```

```java
// Demand control: [Target | ZERO]
// Submitted ZERO; emitted ZERO initial.
// Entry DATA: a.f.g.$/T,N
void root(Box a) { // Entry marking: T only at a.f.g.$.
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y); // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U).
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained NormalTarget(id).
```

## Run-10, backward, field limit 9

```java
// Admitted current NORMAL summaries: none
// Published qualified DEMAND summaries:
//   ret.$/U -> D: p.f.g.NE/T, p.f.g.g.M/T, p.f.g.g.$/T, p.f.NE/T
//   ret.*/U -> D: p.f.g.NE/T, p.f.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.h.*/U -> D: p.f.g.NE/T, p.f.M/T, p.h.M/T, p.f.g.g.M/T, p.f.g.M/T, p.f.g.g.$/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.f.NE/T, p.M/T
//   ret.f.g.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.f.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.h.$/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.h.*/T -> D: p.h.M/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.$/U, p.f.g.M/U, p.f.$/U, p.f.g.NE/U, p.f.M/U, p.$/U, p.f.NE/U, p.M/U
//   ret.f.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U
//   ret.f.g.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U
//   ret.$/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.NE/U, p.f.NE/U
//   ret.*/T -> D: p.f.g.g.$/U, p.f.g.g.M/U, p.f.g.M/U, p.f.g.NE/U, p.f.M/U, p.f.NE/U, p.M/U
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
//   [ret.M/U | p.f.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.*/T]
//   [ret.h.M/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/U | p.f.*/T, p.h.*/T, p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.$/T, p.f.g.$/T, p.h.$/T, p.$/T, p.*/T]
//   [ret.h.$/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.h.M/T | p.h.*/U, p.h.$/U, p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.$/U, p.f.g.*/U, p.f.$/U, p.f.*/U, p.$/U, p.*/U]
//   [ret.f.g.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.f.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.f.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U]
//   [ret.f.g.M/T | p.f.g.g.$/U, p.f.g.g.*/U]
//   [ret.$/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U]
//   [ret.M/T | p.f.g.g.$/U, p.f.g.g.*/U, p.f.g.*/U, p.f.*/U, p.*/U]
//   [ret.$/U | p.f.g.*/T, p.f.g.g.$/T, p.f.g.g.*/T, p.f.*/T]
// Submitted facts:
//   D: ret.M/U, ret.h.M/U
//   D: ret.f.g.$/T, ret.h.M/T, ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW, ret.f.$/FLOW, ret.f.*/FLOW, ret.$/FLOW, ret.f.g.*/FLOW
//   D: ret.f.g.$/T, ret.f.*/T, ret.h.$/T, ret.h.*/T, ret.f.$/T, ret.f.g.*/T, ret.$/T, ret.*/T
// Completed exact-query keys:
//   p.h.$/U
```

```java
// Published: ZERO -> DemandTarget,D; source permission renewed.
void root(Box a) {
    // Entry marking check inputs: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation input: z.M/U,D
}
// Submitted ZERO at normal exit; emitted ZERO initial.
// Demand control [Target | ZERO]; NormalTarget is ignored backward.
```

## Every later pair

For every n >= 0, run-(9+2n) equals the complete run-9 state and
run-(10+2n) equals the complete run-10 state. The equality includes
demand, persisted NORMAL rows, completion cache, actual submissions,
current C5 results and accumulated control state. Field limits increase
without bound. Lean proves each statement by induction and arbitrary-budget
stage equalities, not from this finite rendering.

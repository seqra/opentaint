# Exact-input guard counterexample: complete run trace

16 November 2026. Synthetic data-flow reachability. Production is unchanged.
[Explanation, scope and uncapped proof](bidirectional-exact-input-guard-nontermination-20261116.md).

Notation: `$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
`[entry | output1, output2]` abbreviates separate paired demand rows.
Likewise a summary line with several conclusions lists separate scalar summaries.
All H memberships are plain. E is shown at its original head.
The make annotations aggregate the three actual call submissions to the shared owner.
C5 is paired per row. Companions are included; their FLOW queries yield no marked GEN.
NORMAL lines list admitted current candidates; separately retained saved rows remain available.
Root control annotations are the explicit reference controller; aliases/IR are not modeled. No field write occurs.
Forward inputs are above the declaration and outputs below it; backward placement is reversed.

## Run-1 forward, field limit 1

```java
// Demand: unrestricted run-1
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.$/T.
    // Entry fact: a.f.NE/T,D
    Box x = make(a); // x.M/U,D
    Box y = make(x); // y.M/T,D
    Box z = make(y); // z.M/U,D
    // Observe CM(z.M,U): DemandTarget
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

```java
// Demand rows [entry | paired output]:
//   unrestricted run-1
// Submitted facts:
//   D: p.f.NE/T, p.M/T
//   D: p.M/U
// Emitted initials:
//   D: p.*/T
//   D: p.*/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
//   p.*/T -> D: ret.M/U, ret.h.MUST/U
//   p.*/U -> D: ret.M/T, ret.h.MUST/T
```

## Run-2 backward, field limit 1

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
//   ret.$/U -> D: p.f.NE/T
//   ret.*/U -> D: p.f.NE/T, p.M/T
//   ret.h.$/U -> D: p.f.NE/T, p.M/T
//   ret.h.*/U -> D: p.f.NE/T, p.M/T
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
    return r;
}
// Demand rows [entry | paired output]:
//   [ret.M/U | p.*/T]
//   [ret.h.M/U | p.*/T]
//   [ret.M/T | p.*/U]
//   [ret.h.M/T | p.*/U]
// Submitted facts:
//   D: ret.M/U
//   D: ret.M/T
// Emitted initials:
//   D: ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U
//   N: ret.*/FLOW, ret.h.*/FLOW
//   D: ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T
```

```java
// Published: ZERO -> DemandTarget,D; entry permission renewed.
void root(Box a) {
    // Entry marking checks: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation starts z.M/U,D
}
// Submitted: ZERO at normal exit. Emitted initial: ZERO.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-3 forward, field limit 2

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.$/T.
    // Entry fact: a.f.g.$/T,N
    Box x = make(a); // x.h.MUST/U,N; x.M/U,D; x.h.$/U,N
    Box y = make(x); // y.M/T,D; y.h.MUST/T,N; y.h.$/T,N
    Box z = make(y); // z.M/U,D; z.h.MUST/U,N; z.h.$/U,N
    // Observe CM(z.M,U): DemandTarget plus retained NormalTarget(id)
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]:
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
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
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.$/U -> N: ret.h.MUST/T, ret.h.$/T
//   p.h.$/T -> N: ret.h.MUST/U, ret.h.$/U
// Published DEMAND summaries, qualified refinement view:
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
```

## Run-4 backward, field limit 3

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
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
    return r;
}
// Demand rows [entry | paired output]:
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
```

```java
// Published: ZERO -> DemandTarget,D; entry permission renewed.
void root(Box a) {
    // Entry marking checks: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation starts z.M/U,D
}
// Submitted: ZERO at normal exit. Emitted initial: ZERO.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-5 forward, field limit 4

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.$/T.
    // Entry fact: a.f.g.$/T,N
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y); // z.h.MUST/U,N; z.h.$/U,N; z.M/U,D
    // Observe CM(z.M,U): DemandTarget plus retained NormalTarget(id)
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]:
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
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.MUST/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.$/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.MUST/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.$/T -> N: ret.h.MUST/U, ret.h.$/U
// Published DEMAND summaries, qualified refinement view:
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
```

## Run-6 backward, field limit 5

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
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
    return r;
}
// Demand rows [entry | paired output]:
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
```

```java
// Published: ZERO -> DemandTarget,D; entry permission renewed.
void root(Box a) {
    // Entry marking checks: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation starts z.M/U,D
}
// Submitted: ZERO at normal exit. Emitted initial: ZERO.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-7 forward, field limit 6

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.$/T.
    // Entry fact: a.f.g.$/T,N
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y); // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U): DemandTarget plus retained NormalTarget(id)
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]:
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
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.MUST/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.$/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.MUST/T -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.$/T -> N: ret.h.$/U, ret.h.MUST/U
// Published DEMAND summaries, qualified refinement view:
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
```

## Run-8 backward, field limit 7

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
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
    return r;
}
// Demand rows [entry | paired output]:
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
```

```java
// Published: ZERO -> DemandTarget,D; entry permission renewed.
void root(Box a) {
    // Entry marking checks: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation starts z.M/U,D
}
// Submitted: ZERO at normal exit. Emitted initial: ZERO.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-9 forward, field limit 8

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.$/T.
    // Entry fact: a.f.g.$/T,N
    Box x = make(a); // x.h.MUST/U,N; x.h.$/U,N; x.M/U,D
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N; y.M/T,D
    Box z = make(y); // z.h.$/U,N; z.h.MUST/U,N; z.M/U,D
    // Observe CM(z.M,U): DemandTarget plus retained NormalTarget(id)
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]:
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
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates:
//   p.f.g.$/T -> N: ret.h.MUST/U, ret.h.$/U
//   p.h.MUST/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.$/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.MUST/T -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.$/T -> N: ret.h.$/U, ret.h.MUST/U
// Published DEMAND summaries, qualified refinement view:
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
```

## Run-10 backward, field limit 9

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
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
    return r;
}
// Demand rows [entry | paired output]:
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
```

```java
// Published: ZERO -> DemandTarget,D; entry permission renewed.
void root(Box a) {
    // Entry marking checks: a.M/T,D
    Box x = make(a); // requires a.M/T,D
    Box y = make(x); // requires x.M/U,D
    Box z = make(y); // requires y.M/T,D
    // Backward observation starts z.M/U,D
}
// Submitted: ZERO at normal exit. Emitted initial: ZERO.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Every later pair

For every n >= 0, run-(9+2n) repeats the complete run-9 state and
run-(10+2n) repeats the complete run-10 state, including demand, saved NORMAL
records, submitted packets, current results and control state. Field limits keep
increasing. This is kernel-proved, not inferred from this finite rendering.

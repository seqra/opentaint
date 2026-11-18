# Repaired real-exclusion example: complete run trace

16 November 2026. Synthetic data-flow reachability. Production is unchanged.
[Explanation, scope and uncapped proof](bidirectional-excluded-head-admission-20261116.md).

Notation: `$`=EXACT, `*`=STAR, M=MAY, NE=nonempty MAY, MUST=uniform; N/D=layer.
`[entry | output1, output2]` abbreviates separate paired demand rows.
Likewise a summary line with several conclusions lists separate scalar summaries.
All H memberships are plain. E is shown at its original head.
The make annotations aggregate the three actual call submissions to the shared owner.
C5 is paired per row. Companions are included; their FLOW queries yield no marked GEN.
NORMAL lines list admitted current candidates; separately retained saved rows remain available.
Root control annotations are the explicit reference controller; aliases/IR are not modeled.
Forward inputs are above the declaration and outputs below it; backward placement is reversed.

## Run-1 forward, field limit 1

```java
// Demand: unrestricted run-1
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.MUST/T.
    a.f.g.g = new Box();
    // After write: a.f.NE/T,D
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
    // Entry marking checks: a.M/T,D; a.f.M/T,D; a.f.NE/T,D
    a.f.g.g = new Box(); // Backward outputs above respect the real write.
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
void root(Box a) { // Entry marking: a.f.g.MUST/T.
    a.f.g.g = new Box();
    // After write: a.f.g.MUST/T {g},N
    Box x = make(a); // x.h.MUST/U,D; x.h.$/U,D
    Box y = make(x); // y.h.MUST/T,D; y.h.$/T,D
    Box z = make(y); // z.h.MUST/U,D; z.h.$/U,D
    // Observe CM(z.M,U): DemandTarget
}
// Published: ZERO -> DemandTarget,D.
// NORMAL observation: none.
```

```java
// Demand rows [entry | paired output]:
//   [p.f.NE/T | ret.$/U, ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.M/T | ret.*/U, ret.h.$/U, ret.h.*/U]
//   [p.f.NE/U | ret.$/T, ret.*/T, ret.h.$/T, ret.h.*/T]
//   [p.M/U | ret.*/T, ret.h.$/T, ret.h.*/T]
// Submitted facts:
//   N: p.f.g.MUST/T {g}
//   D: p.h.MUST/U, p.h.$/U
//   D: p.h.MUST/T, p.h.$/T
// Emitted initials:
//   D: p.f.g.*/T {g}, p.h.*/T, p.h.$/T
//   N: p.f.g.*/FLOW {g}, p.$/FLOW, p.f.$/FLOW, p.h.*/FLOW
//   D: p.h.*/U, p.h.$/U
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
//   p.f.g.*/T {g} -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.*/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.h.$/U -> D: ret.h.MUST/T, ret.h.$/T
//   p.h.*/T -> D: ret.h.MUST/U, ret.h.$/U
//   p.h.$/T -> D: ret.h.MUST/U, ret.h.$/U
```

## Run-4 backward, field limit 3

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view:
//   ret.h.$/U -> D: p.f.g.M/T, p.h.M/T, p.h.$/T
//   ret.h.*/U -> D: p.f.g.M/T, p.h.M/T, p.h.$/T
//   ret.h.$/T -> D: p.h.M/U, p.h.$/U
//   ret.h.*/T -> D: p.h.M/U, p.h.$/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]:
//   [ret.h.M/U | p.f.g.*/T {g}, p.h.*/T, p.h.$/T]
//   [ret.h.$/U | p.f.g.*/T {g}, p.h.*/T, p.h.$/T]
//   [ret.h.M/T | p.h.*/U, p.h.$/U]
//   [ret.h.$/T | p.h.*/U, p.h.$/U]
// Submitted facts:
//   D: ret.M/U, ret.h.M/U
//   D: ret.f.g.M/T, ret.h.M/T
// Emitted initials:
//   D: ret.h.$/U, ret.h.*/U
//   N: ret.h.*/FLOW
//   D: ret.h.$/T, ret.h.*/T
```

```java
// Published: ZERO -> DemandTarget,D; entry permission renewed.
void root(Box a) {
    // Entry marking checks: a.f.g.M/T,D; a.h.M/T,D
    a.f.g.g = new Box(); // Backward outputs above respect the real write.
    Box x = make(a); // requires a.f.g.M/T,D; a.h.M/T,D
    Box y = make(x); // requires x.h.M/U,D
    Box z = make(y); // requires y.f.g.M/T,D; y.h.M/T,D
    // Backward observation starts z.M/U,D
}
// Submitted: ZERO at normal exit. Emitted initial: ZERO.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-5 forward, field limit 4

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: ZERO.
void root(Box a) { // Entry marking: a.f.g.MUST/T.
    a.f.g.g = new Box();
    // After write: a.f.g.MUST/T {g},N
    Box x = make(a); // x.h.$/U,N; x.h.MUST/U,N
    Box y = make(x); // y.h.$/T,N; y.h.MUST/T,N
    Box z = make(y); // z.h.$/U,N; z.h.MUST/U,N
    // Observe CM(z.M,U): no DemandTarget plus retained NormalTarget(id)
}
// Published: no new DemandTarget.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]:
//   [p.f.g.M/T | ret.h.$/U, ret.h.*/U]
//   [p.h.M/T | ret.h.$/U, ret.h.*/U]
//   [p.h.$/T | ret.h.$/U, ret.h.*/U]
//   [p.h.M/U | ret.h.$/T, ret.h.*/T]
//   [p.h.$/U | ret.h.$/T, ret.h.*/T]
// Submitted facts:
//   N: p.f.g.MUST/T {g}, p.h.$/T, p.h.MUST/T
//   N: p.h.$/U, p.h.MUST/U
// Emitted initials:
//   N: p.f.g.MUST/T {g}, p.h.$/T, p.h.MUST/T
//   N: p.h.$/U, p.h.MUST/U
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates:
//   p.f.g.MUST/T {g} -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.$/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.MUST/U -> N: ret.h.$/T, ret.h.MUST/T
//   p.h.$/T -> N: ret.h.$/U, ret.h.MUST/U
//   p.h.MUST/T -> N: ret.h.$/U, ret.h.MUST/U
// Published DEMAND summaries, qualified refinement view: none
```

## Run-6 backward, field limit 5

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
```

```java
// Published: none; root is inactive.
void root(Box a) {
    // Entry marking checks: none
    a.f.g.g = new Box(); // Backward outputs above respect the real write.
    Box x = make(a); // requires none
    Box y = make(x); // requires none
    Box z = make(y); // requires none
    // Backward observation starts none
}
// Submitted: ZERO at normal exit. Emitted initial: none; no root Target guidance.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-7 forward, field limit 6

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: none; no entry permission.
void root(Box a) { // Entry marking: a.f.g.MUST/T.
    a.f.g.g = new Box();
    // After write: none
    Box x = make(a); // none
    Box y = make(x); // none
    Box z = make(y); // none
    // Observe CM(z.M,U): no DemandTarget plus retained NormalTarget(id)
}
// Published: no new DemandTarget.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view: none
```

## Run-8 backward, field limit 7

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
```

```java
// Published: none; root is inactive.
void root(Box a) {
    // Entry marking checks: none
    a.f.g.g = new Box(); // Backward outputs above respect the real write.
    Box x = make(a); // requires none
    Box y = make(x); // requires none
    Box z = make(y); // requires none
    // Backward observation starts none
}
// Submitted: ZERO at normal exit. Emitted initial: none; no root Target guidance.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Run-9 forward, field limit 8

```java
// Demand: [Target | ZERO]
// Submitted: ZERO. Emitted initial: none; no entry permission.
void root(Box a) { // Entry marking: a.f.g.MUST/T.
    a.f.g.g = new Box();
    // After write: none
    Box x = make(a); // none
    Box y = make(x); // none
    Box z = make(y); // none
    // Observe CM(z.M,U): no DemandTarget plus retained NormalTarget(id)
}
// Published: no new DemandTarget.
// NORMAL observation: retained; publish ZERO -> NormalTarget(id),N once.
```

```java
// Demand rows [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view: none
```

## Run-10 backward, field limit 9

```java
// Admitted NORMAL summary candidates: none
// Published DEMAND summaries, qualified refinement view: none
Box make(Box p) {
    Box r = new Box();
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
// Demand rows [entry | paired output]: none
// Submitted facts: none
// Emitted initials: none
```

```java
// Published: none; root is inactive.
void root(Box a) {
    // Entry marking checks: none
    a.f.g.g = new Box(); // Backward outputs above respect the real write.
    Box x = make(a); // requires none
    Box y = make(x); // requires none
    Box z = make(y); // requires none
    // Backward observation starts none
}
// Submitted: ZERO at normal exit. Emitted initial: none; no root Target guidance.
// Demand control: [Target | ZERO]. NormalTarget is ignored in backward.
```

## Uncapped quiet suffix

The reference stops naturally at run-5. Every forced run from run-6 onward
has an empty frontier, no new root start, ten retained NORMAL return records
and the retained NORMAL observation. The quiet suffix is proved for every
later run number, not inferred from this finite rendering.

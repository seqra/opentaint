# Protected caller input: an uncapped demand cycle

17 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.

**Resolved under the current approach.** The
[native-bound NORMAL service repair](../design/bidirectional-native-bound-reply-service-20261117.md)
retains the NORMAL observation at run-5 and naturally stops at run-7.
[Updated trace](bidirectional-native-bound-reply-service-trace-20261117.md).
The counterexample and uncapped proof below describe the preceding same-H
policy, with its protected-original fallback. They remain valid for that
historical policy.

The same-flag repair resolves the preceding example but had another open
case. Change the second marking action from h.h.MUST to h.f.g.EXACT. The
first call now produces a protected exact value for the next call. The
selected delivery certificate rejects a protected caller input, although
its full NORMAL body and same-flag native service are ready.

Complete reference states repeat **run-9/run-10 uncapped**, with **39/45
helper DATA demand rows**, one retained NORMAL record and a live root
DemandTarget. Its NORMAL observation remains from **run-5**. The earlier
same-flag repair stays enabled; no guard is disabled.

## Code

```java
class Box { Box f; Box g; Box h; }
// Entry marking: T only at a.f.g.$.
void root(Box a) {
    Box x=make(a).h;
    Box y=make(x).h;
    Box z=make(y).h;
    // Observe CM(z.M,T).
}
Box make(Box p) {
    Box r=new Box();
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.  // H=1
    // CM(p.M,T)       => assign T to r.h.f.g.$. // H=1
    return r;
}
```

`$` = EXACT; `*` = STAR; M = MAY; NE = nonempty MAY; MUST = uniform.
N/D are NORMAL/DEMAND; H is the literal protected membership. E/mx are empty.
Two methods and three sequential calls use one mark T. There is no loop,
recursion, cleaner, configured pass, unresolved model, predefined summary,
static access or field overwrite. These marking actions target a fresh
result; they do not copy an input suffix or return the input object.

## The blocking guard

```text
first call:
    a.f.g.$/T,N,H=0
    make returns ret.h.f.g.$/T,N,H=1
    ordinary h read gives x.f.g.$/T,N,H=1

next call:
    actual / query AP = p.f.g.$/T
    actual layer=NORMAL; input H=1
    full true body returns ret.h.f.g.$/T,N,H=1
    admitted whole same-H NORMAL service exists and applies
    coarse p.f.*/T -> ret.h.M/T,D,H=1 also exists

selected suppressFlaggedReply:
    !originalH = false
    therefore retain the coarse reply

ordinary h read:
    ret.h.M/T,D,H=1 -> y.M/T,D,H=1
```

Here `originalH` is the protection flag of the caller's submitted value,
passed from its existing packet. It is not a new mark or a field exclusion.
Query keys still contain AP/layer; output memberships retain H.

The protected NORMAL exact y.f.g.$/T does not cover all of y.M/T. Exact
reply support does not cover that parent MAY region. Uniform NORMAL coverage
requires MUST; the precise value is EXACT. Old whole/mark/plain reply paths
still reject the protected current row. Its h read renews the same root-MAY
route and the same observation demand.

The first call can use the same-flag repair, because a is plain. The next
calls cannot. This is a caller-binding eligibility gap, not the earlier
unrelated-return or wrong-provider problem.

## Uncapped proof and trace

[Complete per-block trace](bidirectional-protected-original-trace-20261117.md)
contains the cold prefix through run-10, with forward inputs above each
body and summaries below; backward placement is reversed.

| Run | Direction | Helper DATA rows | NORMAL records | Current closure keys | Root |
|---|---|---:|---:|---:|---|
| run-1 | forward | 2 | 0 | 0 | DemandTarget |
| run-2 | backward | 3 | 0 | 0 | entry permission |
| run-3 | forward | 8 | 0 | 0 | DemandTarget |
| run-4 | backward | 15 | 0 | 0 | entry permission |
| run-5 | forward | 22 | 1 | 1 | NORMAL observation + DemandTarget |
| run-6 | backward | 39 | 1 | 0 | entry permission |
| run-7 | forward | 39 | 1 | 1 | NORMAL observation + DemandTarget |
| run-8 | backward | 45 | 1 | 0 | entry permission |
| run-9 | forward | 39 | 1 | 1 | NORMAL observation + DemandTarget |
| run-10 | backward | 45 | 1 | 0 | entry permission |

The [constructive Lean package](../../spec/lean/proposals/protected-original-cycle-20261117/README.md)
proves complete states F/B and:

```text
history(9)=F; history(10)=B
forall n>=0:
    step(2n+9, limit=2n+8, B)=F
    step(2n+10, limit=2n+9, F)=B
therefore history(2n+9)=F and history(2n+10)=B
```

The recurring forward row includes p.f.*/T -> ret.h.M/T,D,H=1; its paired
backward demand is (Dc=ret.h.M/T,Dp=p.f.*/T). Backward handoff retains
(Dc=p.M/T,Dp=ret.h.*/T). F has nonempty demand and a live Target; B renews
entry permission. Earlier forward states do not stop. Each within-run
worklist is at an exact fixed point. No finite cutoff is used in the proof.

All ordinary global, FL(Dc)+1 entry and FL(Dp)+1 output limits remain. Every
steady prepared family and output has a checked bound. E is empty, so the
existing real-hole entry exception is inactive. No new query, suffix history,
raw-summary archive, protection erasure or special seed is introduced.

## Validation and scope

**172 new constructive claims; 6,763 cumulative claims in 356 modules** pass
the source-hash and axiom audit. Every analyzer function is source-identical
to the selected same-flag coordinator; only the analyzed actions and their
reverse transfer change. Allowed foundational axioms are `propext` and
`Quot.sound`; no classical choice or custom axiom is used.

All **11 native fixture/component tests pass**. The unchanged full-program
diagnostic reaches **run-31/POLICY**, with zero NORMAL reports. The proposal
reference retains a NORMAL observation from run-5. This inherited alignment
difference and the lack of complete production integration remain explicit.
The finite native cutoff is not the nontermination proof.

No repair is selected in this report. The next phase investigates certificates
for the actual bound NORMAL images, with protection transported by the existing
native operation. The conditional observation-preservation theorem is not
refuted. Production is unchanged. Large captures and compiled artifacts are
external under `report-data-archive/opentaint-w3/docs/reports/data/protected-original-cycle-20261117/`.

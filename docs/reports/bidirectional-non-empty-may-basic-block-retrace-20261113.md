# Retrace with basic-block demands

13 November 2026. Hypothetical BB summarization experiment. No production
code is changed. Follow [the proof guide](../../spec/proof-guide.md).

**Result:** the read BB becomes precise by run-4. The original cycle changes,
but the unchanged enclosing method restriction creates another cycle from
run-5. Both BB bodies can use saved NORMAL summaries while the method still
publishes DEMAND.

## 1. Program and boundary policy

Use [the same acyclic example](bidirectional-non-empty-may-acyclic-nontermination-20261113.md):

```java
class Box { Box f; Box g; }

void main(boolean flag) {
    Box a = sourceAtF();
    Box b = choose(a, flag);       // call 1
    Box c = choose(b, flag);       // call 2: SAME choose owner
    sinkAnywhere(c);
}

Box choose(Box p, boolean flag) {
    if (flag)
        readBB: {
            return p.f.g;
        }
    else
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
}
```

The source assigns T to `a.f` and all descendants, including `a.f`:
`a.f.MUST/T,N`. The sink checks `c.MAY/T`. Keep FULL mode, aliases disabled,
Empty E/mx, H=false, limits `1,1,2,3,...` and no hard iteration limit.

The labels identify normal-flow BB regions, not new real function calls.
The entry-dispatch and synthetic common-exit BBs carry identities. Their
saved NORMAL summaries preserve support and ports. `main` is one straight
normal-flow region here. Exceptional alternatives are not needed by the
witness.

Use [the selected C2/C5](../../spec/non-empty-may.md) separately at each BB
and the enclosing method:

```text
saved NORMAL replay on the original offer
then C2 for current analysis/subscription
local C5 before a newly analyzed BB summary is published
summary application preserves the enclosing original premise
enclosing method C5 still runs at method exit
```

Keep opposite-direction STAR-inside matching. Do not add the loop-repeat
growth gate to acyclic BBs. Do not skip C2 because saved replay succeeded.
Do not add new subsumption rules. These choices define the candidate being
retraced; BB summarization is not implemented by this investigation.

Notation: `F=FLOW`, `M=MAY`, `NE=non-empty MAY`, `U=MUST`, `N=NORMAL`,
`D=DEMAND`; `[Dc ; Dp]` is a complete incoming paired demand. Every listed
initial starts as an identity. The annotations show retained witness rows,
not exhaustive dumps. Extra queries and NORMAL records are allowed; none
are silently reset between runs.

## 2. Overview

All DATA rows below have mark F.

| Run | readBB principal publication | writeBB | choose principal DEMAND |
| --- | --- | --- | --- |
| run-1 F, limit 1 | `p.* -> ret.M,D` | Learn NORMAL `p.* -> ret.f.*` | `p.* -> ret.M,D` |
| run-2 B, limit 1 | `ret.* -> p.f.NE,D` | Saved reverse replay | `ret.* -> p.M,D` |
| run-3 F, limit 2 | `p.f.* -> ret.M,D`; reject offered root STAR | Saved replay | `p.f.* -> ret.M,D` |
| run-4 B, limit 3 | NORMAL `ret.* -> p.f.g.*` | Saved reverse replay | `ret.* -> p.f.M,D` |
| run-5 F, limit 4 | Saved replay suffices | Saved replay | `p.f.U -> ret.f.NE,D`; `p.f.* -> ret.M,D` |
| run-6 B, limit 5 | Saved replay | Saved reverse replay | `ret.* -> p.f.M,D`, plus possible side rows |

The key run-2 change: readBB's `p.f.NE` cannot be merged with writeBB's
`p.M` in **readBB's own storage**. They have different owners. They can
still merge when applied in the enclosing method.

## 3. Run-1: forward, limit 1

```java
// CHOOSE: no demand; submitted p.f.U/T,N and derived p.M/T,D.
// Run-1 abstract initial p.*/F,N; ordinary mark requests supply T.
Box choose(Box p, boolean flag) {
    if (flag)
        // readBB: no demand; submitted p.*/F,N; initial p.*/F,N.
        readBB: {
            return p.f.g;       // Unknown-suffix reads -> ret.M/F,D.
        }
        // readBB published: p.*/F -> ret.M/F,D.
    else
        // writeBB: no demand; submitted p.*/F,N; initial p.*/F,N.
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // writeBB published NORMAL: p.*/F -> ret.f.*/F,N.
}
// CHOOSE NORMAL: p.*/F -> ret.f.*/F,N.
// CHOOSE DEMAND: p.*/F -> ret.M/F,D.
```

`main` submits ZERO,N and starts ZERO,N, without demand. The source gives
`a.f.U/T,N`; ordinary choose applications give `b.M/T,D` and `c.M/T,D`.
The sink publishes `ZERO -> DemandTarget,D` from main's BB and method.

## 4. Run-2: backward, limit 1

Backward summaries appear above their block; demand and inputs appear below.

```java
// CHOOSE published: ret.*/F -> p.M/F,D.
Box choose(Box p, boolean flag) {
    if (flag)
        // readBB published: ret.*/F -> p.f.NE/F,D.
        readBB: {
            return p.f.g;       // Reverse candidate p.f.g.*/F,N.
                               // Global limit 1 cuts it to p.f.NE/F,D.
        }
        // readBB demand [ret.M/F ; p.*/F].
        // Submitted ret.$/F,N and ret.*/F,N; same identity initials.
    else
        // writeBB saved opposite view: ret.f.*/F -> p.*/F,N.
        writeBB: {
            Box q = new Box();
            q.f = p;            // Reverse root STAR reads unknown f -> p.M/F,D.
            return q;
        }
        // No current writeBB DATA demand or fresh DATA initial.
        // Saved replay still runs before that empty C2 result.
}
// CHOOSE demand [ret.M/F ; p.*/F].
// Submitted ret.M/T,D at call 2 and derived ret.M/T,D at call 1.
// Initials ret.$/F,N and ret.*/F,N.
```

At the method level, `p.M,D` covers the cut child under the same original.
Inside readBB, the other branch's provider is absent. Its own handoff keeps
`[p.f.NE/F ; ret.*/F]` for run-3.

Main's demand is `[Target ; ZERO]`, its submitted fact and initial are
ZERO,N. Its reverse sink seed is `c.M/T,D`; both calls reach `a.M/T,D`.
That overlaps the actual named source `a.f.U/T`, records source permission,
and publishes `ZERO -> DemandTarget,D`.

## 5. Run-3: forward, limit 2

```java
// CHOOSE demand [p.M/F ; ret.*/F].
// Call 1 p.f.U/T,N -> initials p.f.*/F,N and prefix p.$/F,N.
// Derived call 2 p.M/T,D -> initials p.$/F,N and p.*/F,N.
Box choose(Box p, boolean flag) {
    if (flag)
        // readBB demand [p.f.NE/F ; ret.*/F].
        // Submitted p.f.*/F,N -> initial p.f.*/F,N.
        // Submitted p.*/F,N -> NO admission: ancestor STAR cannot descend.
        // Submitted p.$/F,N -> NO admission.
        readBB: {
            return p.f.g;       // p.f.* reads unknown g -> ret.M/F,D.
        }
        // readBB published: p.f.*/F -> ret.M/F,D.
    else
        // No current writeBB DATA demand; saved NORMAL replay first.
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // No new writeBB query is needed for the witness.
}
// CHOOSE DEMAND: p.f.*/F -> ret.M/F,D.
// The old root p.* -> ret.M route lacks current readBB admission.
```

This is real progress. The method's write branch no longer erases readBB's
own f frontier. Main still receives the partial query's `b.M/T,D`, then
`c.M/T,D`, and publishes its ZERO-to-DemandTarget row. Main's incoming
`[Target ; ZERO]`, submitted ZERO,N and initial ZERO,N are unchanged.

## 6. Run-4: backward, limit 3

```java
// CHOOSE DEMAND: ret.*/F -> p.f.M/F,D.
Box choose(Box p, boolean flag) {
    if (flag)
        // readBB NORMAL: ret.*/F -> p.f.g.*/F,N.
        readBB: {
            return p.f.g;       // Depth 2 fits its own paired output budget 2.
        }
        // readBB demand [ret.M/F ; p.f.*/F].
        // Submitted ret.$/F,N and ret.*/F,N; same identity initials.
    else
        // writeBB saved reverse replay gives p.M/F,D.
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // No current writeBB DATA demand or initial.
}
// CHOOSE demand [ret.M/F ; p.f.*/F].
// Submitted ret.M/T,D -> initials ret.$/F,N and ret.*/F,N.
// Method C5 rebases the write replay's p.M to p.f.M, keeping D.
```

ReadBB has no outgoing DATA demand on this principal route. Its saved
forward opposite view is now `p.f.g.*/F -> ret.*/F,N`.
Main's ordinary ZERO/Target route again reaches the source and renews its
permission. Stopping the trace here would miss the next effect.

## 7. Run-5: the method cut recreates a coarse input

```java
// CHOOSE demand [p.f.M/F ; ret.*/F].
// Call 1 submitted p.f.U/T,N -> dedicated initial p.f.U/F,N.
// Derived call 2 p.f.NE/T,D -> initial p.f.*/F,N.
Box choose(Box p, boolean flag) {
    if (flag)
        // No principal current readBB DATA demand or new local initial.
        // Replay the run-4 NORMAL opposite view FIRST.
        readBB: {
            return p.f.g;
        }
        // Applied to p.f.U/F,N -> ret.U/F,N.
        // Applied to p.f.*/F,N -> ret.M/F,D:
        // STAR-inside matching is legal for this opposite-direction record.
        // These are applications, not newly analyzed readBB summaries.
    else
        // Saved NORMAL writeBB relation; no new local initial is needed.
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // Applied to p.f.U/F,N -> ret.f.f.U/F,N, still PRECISE.
}
// Raw method candidate: p.f.U/F -> ret.f.f.U/F,N.
// Method Dp = ret.*/F, so budget min(4,0+1)=1.
// CHOOSE published: p.f.U/F -> ret.f.NE/F,D.
// Its actual binding at call 1 supplies b.f.NE/T,D.
// That offer starts p.f.* at call 2; saved read replay then publishes:
//     p.f.*/F -> ret.M/F,D.
// Separate NORMAL p.f.U/F -> ret.U/F is retained too.
```

This is the full forward chain, without assuming a recurring NE offer:

```text
a.f.U/T,N
  -> method initial p.f.U/F,N
  -> saved writeBB: ret.f.f.U/F,N
  -> METHOD C5, budget 1: ret.f.NE/F,D
  -> current choose summary applied at call 1: b.f.NE/T,D
  -> call 2 C2 at p.f.M/F: p.f.*/F,N
  -> saved opposite readBB: ret.M/F,D
  -> METHOD C5: p.f.*/F -> ret.M/F,D
```

Main's BB and method still use `[Target ; ZERO]`, ZERO,N admission. The
second call supplies `c.M/T,D`, hence `ZERO -> DemandTarget,D` is published.
A NORMAL report can coexist with this row.

The saved whole-method NORMAL writer may also supply precise
`b.f.f.U/T,N` before current analysis. Replay success does not cancel C2.
The read route can supply `b.U/T,N`. Neither silently removes the D/NE
membership under the selected rules: MUST canonicalization is within the
same layer, with no new MUST-to-NE deletion. The aligned NORMAL FLOW law
requires STAR premises and STAR conclusions; the raw MUST/MUST candidate
does not pass that guard. After the cut, STAR-to-NE backing is not selected
either. Extending those rules would require a separate proof.

## 8. Run-6 and the later cycle

```java
// CHOOSE principal DEMAND: ret.*/F -> p.f.M/F,D.
Box choose(Box p, boolean flag) {
    if (flag)
        // Saved readBB NORMAL, read in its original backward direction.
        readBB: {
            return p.f.g;
        }
        // ret.*/F,N -> p.f.g.*/F,N. No new local initial needed.
    else
        // Saved writeBB NORMAL, read in the opposite direction.
        writeBB: {
            Box q = new Box();
            q.f = p;
            return q;
        }
        // ret.*/F,N -> p.M/F,D. No new local initial needed.
}
// CHOOSE principal demand [ret.M/F ; p.f.*/F].
// Call 2 submitted ret.M/T,D -> initials ret.$/F,N and ret.*/F,N.
// Its result gives call 1 submitted ret.f.M/T,D; admission is nonempty.
// The shared current ret.* -> p.f.M row applies to that original offer.
// Method C5 rebases p.M to p.f.M; handoff restores [p.f.M/F ; ret.*/F].
```

Main again admits ZERO,N through `[Target ; ZERO]`. The sink seed reaches
`a.f.M/T,D`, overlapping the source at `a.f.U/T`. It renews real source
permission and publishes `ZERO -> DemandTarget,D`.

Side rows from the other run-5 demand may coexist. They do not permit
mixing entry permission or budgets across pairs. The witness proof is
membership inclusion, not equality of the whole frontier.

For every later odd run, the incoming pair `[p.f.M/F ; ret.*/F]` repeats
the run-5 derivation. Its source still admits `p.f.U`; the precise write
has concrete depth 2, while that pair's output budget is still 1. The same
NE input and STAR/MAY route are therefore produced. For every later even
run, `[ret.M/F ; p.f.*/F]` repeats the run-6 derivation. The saved NORMAL
BB providers are already available. No new readBB/writeBB body analysis
is needed for these replay witnesses.

The repeating method pair is:

```text
run-5, run-7, run-9, ...: p.f.*/F   -> ret.M/F,D
run-6, run-8, run-10,...: ret.*/F   -> p.f.M/F,D
```

Thus BB demand improves local refinement and can eliminate repeated body
analysis, but does not ensure empty enclosing-method demand. The later
work-producing chain is:

```text
NORMAL BB composition -> method FL(Dp)+1 cut -> NE offer
    -> STAR initial -> saved opposite read -> MAY method demand
```

No new summary subsumption, saved-replay gate or method-cut exception is
selected by this investigation.

## 9. Checked proof and limits

[BbTrace.lean](../../spec/lean/proposals/non-empty-may-acyclic-cycle-20261113/BbTrace.lean)
adds 25 checked declarations: the local run-2 cut, run-3 admission/rejection,
run-4 NORMAL relation, actual run-5 NE offer, saved opposite replay, paired
method C5 and unbounded later witness recurrence. It imports the selected
C2/C5 and the original example's prefix-transfer model.

This is a constructive witness projection, not a BB-decomposition or
whole-production-driver implementation. The report checks the scope/control
embedding; incidental queries and additional NORMAL records remain allowed.
The repeated row is not declared redundant on the strength of this trace.

Reproduce the reference, original cycle and BB checks:

```sh
python3 spec/lean/proposals/non-empty-may-acyclic-cycle-20261113/check.py \
    --out /tmp/non-empty-may-bb-retrace-check
```

The checker rejects custom axioms, classical choice and unfinished proofs.
Result: **PASS, 6 modules, 125 audited declarations**. The external receipt
is `non-empty-may-acyclic-cycle-20261113/bb-proofs-v2/receipt.json` under the
[report data archive](EXTERNAL_DATA.md); the first failed preparation is
kept separately and is not used as validation evidence.
No project scan was run. Historical latest reached/completed/accepted-forward
positions remain OWASP **run-11/11/11**, Conductor **run-8/7/7**, Stirling-PDF
**run-11/10/9**. This model explicitly traces through run-6 and proves the
principal later recurrence without an iteration limit.

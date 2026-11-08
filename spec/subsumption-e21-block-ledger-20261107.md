# E21: block trace and remaining proof boundary

7 November 2026. Reference design review. No new analyzer run.
The latest historical native capture completed **run-5** without the finding.
This document supports [E21](subsumption-principal-examples-20261107.md#e21-deep-no-leave-loop-creates-an-exact-target-obligation).

**This earlier ledger is not an enumerated final fixed point.** The new
[closed-family review](descendant-intersection-and-flow-completion-review-20261107.md#3-a-counterexample-to-removing-all-completion-under-the-current-loop-gate)
computes one-body reference transaction families through run-4 and compares
the run-5 gate. It does not close saved-repeat delivery. The
[corrected run-4 fixed point](subsumption-loop-and-gap-audit-20261108.md#24-run-4-backward-field-limit-3-close-saved-replay-first)
reaches ANY and separates parent completion from exported local rows.
Native grammar/port/root correspondence remains open. The comments below give the known
commands and complete one-body candidate families. The complete retained
sets, after current/saved replay, loop feedback and subsumption, remain to be
computed. A three-row necessary route is not a complete handoff snapshot.
Do not use it to prove that another DATA pair is absent.

## Notation and common operations

`F=FLOW`, `?=ANY`, `N=NORMAL`, `D=DEMAND`. `f^n` means n copies of field f.
`root` is x with no fields. T is the source mark. All these scalar examples
have Empty E and H=false. The physical repeat port is 5. First entry,
feedback, backward discovery and logical Target ports remain distinct.
There is no physical forward leave from the `while(true)` loop.

`Dk` is the complete incoming paired view. Write its rows as `(Dc,Dp)`.
`Jk` contains every admitted initial command, including companions, for every
real submitted actual. `Rk` is the final admitted summary basis. Only Rk forms
the next handoff. Raw candidates removed by subsumption are not hidden guides.

For each admitted nonzero identity I, the complete one-body DATA families are:

```text
forward(I):
    keep I through sourceFFFF; apply x=x.f
    x.f^n/tail/mark -> x.f^(n-1)/tail/mark, n>0
    x.*/mark       -> x.?/mark, DEMAND
    x.$/mark       -> no DATA

backward(I):
    keep I through sink; prepend f; apply current global field cap
    keep the resulting DATA through sourceFFFF
    if actual T matches the same physical source at ffff: also emit Reach/Target

ZERO forward:
    keep Reach; if the real source is permitted, emit ffff.$/T,N
    apply global cap and x=x.f to that source value

ZERO backward:
    keep Reach; the reached sink with Target permission emits root.$/T,N
    its reverse read emits f.$/T,N

sink observation:
    matching real T gives DemandTarget for D support, NormalTarget for N support
    F alone does not satisfy the T check

Rawk = union of these families for ALL commands in Jk and real saved applications
Rk   = final canonical union of C5(d,raw), for ALL raw in Rawk and ALL d in Dk
```

Source/Target effects still require their actual rule and control permission.
Every paired C5 result keeps its original, support, H and exact ports. ZERO
exit rejects DATA; DATA exit rejects Reach. Whole-FLOW normalization changes
raw EXACT/FLOW to stored STAR/FLOW. Concrete STAR identities remain DEMAND.

The optional completion view in the earlier draft adds endpoint-prefix
FLOW/ANY self-pairs and one complete DATA/DATA head pair. Treat any trace
which uses those extra pairs as conditional on that candidate policy.

## Run-1: forward, limit 1

```java
void deep(Node x) {
    // BL demand: none. Submitted: configured root ZERO.
    BL: { }
    // BL output: ZERO reaches L first entry. No local-x DATA default.

    // L demand: none.
    // Submitted: reached ZERO; source ffff.$/T,N -> cap1 f.?/T,D
    //            -> read root.?/T,D. Run-1 abstraction/request slots follow.
    L: while (true) {
        sourceFFFF(x); // Exact T at x.f.f.f.f, same source in every run.
        x = x.f;
        sinkExactT(x);
    }
    // L raw summary families:
    //   ZERO     -> Reach,N                    [feedback; no forward leave]
    //   ZERO     -> root.?/T,D                  [real capped source]
    //   ZERO     -> DemandTarget               [logical Target exit]
    //   root.*/F -> root.?/F,D                  [feedback]
    //   root.*/T -> root.?/T,D                  [requested T actor]
    //   root.*/T -> DemandTarget               [real sink check]
    // Retained R1: canonical final basis of these families at each interface.
    // The plain T DATA diagonal can be FLOW-backed; do not assume it survives.

    // AL demand: no reached physical input. Submitted: none.
    AL: { } // Unreachable; a logical Target is not a CFG leave.
    // AL summaries: none from execution. Do not insert a DATA frame.
}
```

The NORMAL Reach singleton is saved. A forward NORMAL unary row does not
itself become outgoing refinement demand. Real DEMAND and Target rows do.

## Run-2: backward, limit 1

```java
void deep(Node x) {
    // BL demand/submitted: no free DATA frame. Only actual L leaves can arrive.
    BL: { }
    // BL summaries: ordinary compositions of those actual leaves only.

    // L demand: reverse ALL selected R1 rows, retaining each pair and port.
    // Known DATA rows: (root.?/T,ZERO), (root.?/F,root.*/F).
    // If retained: (root.?/T,root.*/T).
    // Known control routes: (Target,ZERO), (Target,root.*/T).
    // Submitted: actual backward ZERO discovery; sink root.$/T,N;
    // reverse read f.$/T,N; all real feedback/current/saved effects.
    L: while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkExactT(x);
    }
    // L raw families: ZERO->Reach; permitted ZERO->f.$/T,N;
    //   every I in J2 -> cap1(f.I); actual source Reach/Targets for T actors.
    // Concrete included FLOW rows, before final replacement:
    //   raw root.$/F -> f.$/F,N
    //   stored root.*/F -> f.*/F,N               [saved NORMAL grower]
    //   f.*/F -> f.?/F,D                         [outgoing DATA pair]
    // T STAR actors add the authorized FLOW companion, with their own C5 exit.
    // Retained R2: ALL such paired results after canonical replacement.
    // Do not retain a removed T diagonal as extra next-run guidance.

    // AL submitted: no forward physical leave; backward discovery uses its
    // existing overlay, not a new AL DATA default.
    AL: { }
    // AL summaries: only actual overlay work; no independent DATA frame.
}
```

Known J2 commands include root.EXACT/F,N, f.STAR/F,N and f.EXACT/T,N from the
exact reverse-read fact. A real f.ANY/T,D can also select f.STAR/T,D and its
companion. This included list is not an exact J2 enumeration.

## Run-3: forward, limit 2

```java
void deep(Node x) {
    // BL demand: actual previous source/Target route. Submitted: admitted ZERO.
    BL: { }
    // BL output: ZERO to first L entry. No guessed x-to-x DATA frame.

    // L demand: reverse ALL selected final R2 rows, including backward NORMAL
    // ZERO rows. Known DATA family: (f.?/F,f.*/F).
    // Submitted: real source cap2 ff.?/T,D -> read f.?/T,D;
    // all actual current/saved feedback and typed ZERO re-entry.
    // Saved opposite root.*/F -> f.*/F can shrink a supplied suffix.
    L: while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkExactT(x);
    }
    // L raw families: ZERO->Reach; permitted ZERO->f.?/T,D;
    // every I in J3 -> forward(I); real T sink Targets with that I.
    // Included actual candidates:
    //   f.$/T,D -> root.$/T,D -> DemandTarget
    //   f.*/T,D -> root.*/T,D
    //   f.*/F,N -> root.*/F,N                    [real NORMAL shrinker]
    // That shrinker also follows from R2's FLOW DATA family, without completion.
    // Retained R3: ALL paired results after canonical replacement;
    // FLOW backing can remove the plain T diagonal, not its control Target.

    // AL demand/submitted: no physical forward leave.
    AL: { }
    // AL summaries: none from physical execution.
}
```

The same-head f.ANY/T,D can select f.EXACT/T,D for an exact entry selector.
An ordinary root.STAR actual under a deeper f demand rejects instead. These
are different C2 cells. The NORMAL unary FLOW shrinker is saved; its NORMAL
forward row does not enter the handoff as refinement demand.

## Run-4: backward, limit 3

```java
void deep(Node x) {
    // BL demand/submitted: only actual admitted control routes and L leaves.
    BL: { }
    // BL summaries: real compositions only; no independent DATA frame.

    // L demand: ALL final R3 paired rows. Known routes include
    // (Target,f.$/T) and (f.?/T,ZERO). Keep distinct physical ports.
    // Submitted: sink root.$/T,N, read f.$/T,N and real opposite NORMAL
    // applications ff.$/T,N, fff.$/T,N. All real feedback also participates.
    L: while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkExactT(x);
    }
    // L raw families: ZERO controls/sink seed; ALL I in J4 -> cap3(f.I);
    // real source Reach/Target when T reaches the physical source.
    // Included principal source route:
    //   admitted ff.*/T,D -> fff.*/T,D -> source Reach/Target
    //   ff.*/T -> Reach,D; ff.*/T -> DemandTarget [exact actual ports]
    // Companion ff.*/F,N under the SAME ZERO exit: no DATA output.
    // Conditional extra FLOW self-pair at f can instead admit:
    //   ff.*/F -> ff.?/F,D, paired budget 2.
    // Retained R4: ALL C5 outputs after final replacement. Other DATA/DATA
    // pairs must be checked before asserting this completion is necessary.

    // AL demand/submitted: no independent physical DATA route.
    AL: { }
    // AL summaries: no extra default frame or source permission.
}
```

The FLOW companion cannot satisfy the concrete source guard. The T actor
grants the real source permission. The pair `(f.ANY/T,ZERO)` admits its Reach
or Target effect, but rejects every DATA conclusion, including FLOW.

## Run-5: forward, limit 4

```java
void deep(Node x) {
    // BL demand: actual R4 control/source route. Submitted: configured ZERO.
    BL: { }
    // BL output: ZERO reaches first L entry; same source is permitted.

    // L demand: reverse ALL final selected R4 rows. Principal routes include
    // (ZERO,ff.*/T), (Target,ff.*/T), (f.$/T,ZERO).
    // If retained, (ff.?/F,ff.*/F) is another complete DATA pair.
    // Submitted: real source ffff.$/T,N -> read fff.$/T,N;
    // all actual current/saved feedback. This precise source is not a D upgrade.
    L: while (true) {
        sourceFFFF(x);
        x = x.f;
        sinkExactT(x);
    }
    // L raw families: ZERO->Reach and real source result; every admitted
    // I in J5 -> forward(I); T Targets only after the real sink is reached.
    // Conditional route if a retained fine FLOW pair admits repeat delivery:
    //   fff.$/T,N -> ff.$/T,N -> f.$/T,N -> root.$/T,N
    //   ZERO -> NormalTarget at the configured root.
    // Each shrinking step uses the real saved NORMAL FLOW summary.
    // Retained R5 and the unconditional finding: NOT established by this ledger.

    // AL submitted: none. NormalTarget uses the logical boundary protocol.
    AL: { }
    // AL summaries: none from physical forward execution.
}
```

A same-port ff.ANY/FLOW entry selects raw fff.STAR/FLOW,N. Cutting that raw
source to depth 2 cannot produce the same depth-3 command. This local fact
does not prove that the complete final R4 basis contains that guide.

## Checked results and open questions

The [operator model](lean/proposals/subsumption-initial-demand-20261107/E21OperatorLedger.lean)
checks eight transactions: B2 root EXACT/FLOW; its NORMAL public grower;
F3 shrinker from the original FLOW demand; B4 T plus companion; rejection of
all their DATA by ZERO exit; the conditional self-pair's B4 FLOW result;
the F5 raw/cut command difference; and ancestor-STAR rejection.
These are operator checks, not a complete driver proof.

The new review computes every scalar family in its declared reference
grammar and proves a kept-gate counterexample, including both source C5
images. It does not supply a native all-port fixed point. Native grammar,
physical ports and root scheduling remain correspondence obligations.

The present gate checks a growing result before repeat delivery. The new
proof keeps that order. Moving saved non-growing replay before it remains
a different design. The completed case can retain both NormalTarget and
DemandTarget; a finding proof is not a natural-stop proof.

Do not infer necessity from E28 or the old incomplete list. Use the new
closed-family result within its stated scope. No runtime change follows
from this earlier ledger.

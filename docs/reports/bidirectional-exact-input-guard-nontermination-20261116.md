# An exact input still renews a coarse mark question

Historical counterexample to the preceding policy. The
[complete-point service repair](bidirectional-complete-point-service-20261116.md)
now stops this reference naturally at run-5 (run-7 with delayed readiness).
The run-9/run-10 recurrence below remains the checked before-change result.
Production is unchanged; its finite diagnostic still reaches run-31.

16 November 2026. Synthetic data-flow reachability. FULL marks. Follow
[proof-guide.md](../../spec/proof-guide.md). Production is unchanged.

**Result:** the latest [consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md)
has an uncapped counterexample with **no loop, recursion, cleaner, special
pass rule, field overwrite or unresolved method**. The complete reference
repeats its **run-9/run-10** states forever: 70 forward / 82 backward
qualified demand rows, ten retained NORMAL return records and a live root
DemandTarget.

All real field exclusions are empty. The latest NORMAL-MUST/real-E head
exception stays enabled but is ineligible throughout this example. Ordinary
C2 starts retain their original global and Dc+1 caps. Every run reaches its
within-run fixed point; the repetition is between completed runs.

## 1. Code and rules

```java
class Box { Box f; Box g; Box h; }

// Entry marking rule: assign T only at the exact point a.f.g.$.
void root(Box a) {
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observation rule: CM(z.M,U).
}

Box make(Box p) {
    Box r = new Box();
    // Four ordinary unary marking rules at this point:
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
```

All three calls share the same make owner. Both bodies and the call graph
are acyclic. The only ordinary transfers in make are fresh allocation and
return. Every configured action assigns a literal full mark to a fresh
result. The four conditions are positive unary checks, not ND cubes.
No action introduces MAY directly or acts as a pass.

The entry rule marks the point a.f.g, not its descendants. Therefore the
deep p.f.g.g condition cannot hold for the first actual. The broad p.M
condition can hold and provides the valid NORMAL h route. It is essential
to keep that action in the example: its reverse demand renews the broad
input question.

## 2. Decisive facts

Notation: `$`=EXACT, `*`=correlated STAR, M=MAY, NE=nonempty MAY,
MUST=uniform, N/D=layer. All E/mx are empty and all H memberships are plain.
`[Dc | Dp]` is an entry selector with its original paired output selector.

Consider the recurring row `[p.M/T | ret.*/U]` after the global limit fits
the exact input:

```text
actual:                   p.f.g.$/T, NORMAL
base first-field initial: p.f.*/T, DEMAND
existing FLOW companion:  p.f.*/FLOW, NORMAL
existing prefix probe:    p.$/FLOW, NORMAL
fine qualified initial:   p.f.g.$/T, NORMAL
```

Base C2 stops at the first new field. It loses both the remaining known g
and the fact that the actual ends exactly there. A qualified p.f.NE row can
also start the fine p.f.g.$ query, since g refines that row's nonempty suffix.
The fine query does not cancel the independent base query.

```text
coarse p.f.*/T,D:
    deep CM(p.f.g.g.M,T) may hold -> ret.M/U,D
    broad CM(p.M,T) may hold     -> ret.h.MUST/U,D

fine p.f.g.$/T,N:
    deep CM(p.f.g.g.M,T) cannot hold -> no root result
    broad CM(p.M,T) holds           -> ret.h.MUST/U,N
```

The coarse conditional summary applies to the real exact point. MAY is an
independent uncertain output, so application does not recover the lost
guard dependency from the known input suffix. The native component test
checks this binding directly:

```text
current summary: p.f.*/T -> ret.M/U,D
actual:          p.f.g.$/T,N
reply:           ret.M/U,D
```

The actual call chains contain both:

```text
coarse: a.f.g.$/T,N -> x.M/U,D -> y.M/T,D -> z.M/U,D
normal: same point -> x.h.MUST/U,N
                         -> y.h.MUST/T,N -> z.h.MUST/U,N
```

Paired C5 also produces exact h images. A NORMAL result under h cannot
cover the whole root-MAY region; the selected whole-region coverage law
correctly keeps the root-MAY reply. No unsupported MUST replay is needed.
The observation has a NORMAL witness from run-3, plus an independent DEMAND
witness. The retained NORMAL report does not cancel DemandTarget.

## 3. Per-iteration trace

The [complete annotated trace](bidirectional-exact-input-guard-trace-20261116.md)
embeds every demand row, submitted fact, initial and admitted NORMAL/DEMAND
summary through **run-10**, for both analyzable blocks, root and make.
Forward inputs are above each declaration, summaries below its end;
backward placement is reversed. Grouped output lists abbreviate separate
scalar paired rows. The variables are those from the code.

The table counts qualified rows and retained NORMAL return records in the
marked-return/control reference, not all production engine facts.

| Completed run | Direction / field limit | Qualified rows | NORMAL return records | Root Target / backward permission | NORMAL observation retained |
|---|---|---:|---:|---|---|
| run-1 | F / 1 | 4 | 0 | DemandTarget | no |
| run-2 | B / 1 | 14 | 0 | permission renewed | no |
| run-3 | F / 2 | 26 | 6 | DemandTarget | yes |
| run-4 | B / 3 | 42 | 6 | permission renewed | yes |
| run-5 | F / 4 | 44 | 10 | DemandTarget | yes |
| run-6 | B / 5 | 69 | 10 | permission renewed | yes |
| run-7 | F / 6 | 68 | 10 | DemandTarget | yes |
| run-8 | B / 7 | 82 | 10 | permission renewed | yes |
| run-9 | F / 8 | 70 | 10 | DemandTarget | yes |
| run-10 | B / 9 | 82 | 10 | permission renewed | yes |
| run-(9+2n) | F / (8+2n) | 70 | 10 | DemandTarget | yes |
| run-(10+2n) | B / (9+2n) | 82 | 10 | permission renewed | yes |

Run-1 cuts the two-field exact entry assignment to a.f.NE/T,D. That is a
real cut; the new NE tail is used. Backward run-2 creates both qualified
f.NE and broad M input rows. From run-3 the exact source point fits the
global limit, and qualified rows produce legitimate NORMAL h results.
The base row still starts only at f.

Later reverse STAR result queries intersect the h assignments and emit the
broad p.M operands. Paired C5 keeps those broad input questions. In root,
the three reversed calls deliver a broad T demand to the exact entry
marking rule and renew permission for the next forward run. The recurring
actuals are derived by the call pipeline, not supplied as an external
repeating packet.

The three calls share one owner. Later calls with root-MAY actuals keep
root input questions in that owner's demand. Those questions also admit
the first call's exact point through its first-field projection. This is
feedback through shared analysis queries, not recursion in the code.

## 4. Uncapped nontermination proof

Let F be the complete frozen state after run-9 and B the state after
run-10. Each includes qualified demand, retained NORMAL records, submitted
domains, admitted current results, reply packets and control state.

The [constructive Lean package](../../spec/lean/proposals/exact-input-guard-cycle-20261116/README.md)
checks the cold prefix and proves:

```text
forall n >= 0:
    State(9+2n)  = F
    State(10+2n) = B

F.rows has 70 members; B.rows has 82 members.
F.saved = B.saved; length = 10.
F.report = true; F.observationActive = true; B.sourceAllowed = true.

forall n >= 0, m in {T,U}:
    [ret.M/flip(m) | p.*/m] belongs to State(9+2n).rows
    [p.M/m | ret.*/flip(m)] belongs to State(10+2n).rows
```

Thus the same nonempty qualified demand returns after every later forward
pair, not merely two sampled runs. No later forward stop test succeeds,
and no earlier forward stop was skipped in the cold prefix.

The proof first checks each cold transition and another complete worklist
sweep at its result. It then checks delivery/publication stages for **every
budget n+8**, proves the steady transitions and connects them to the
unbounded `1,1,2,3,...` schedule by induction. The final within-run sweep
is a fixed point for every such budget. Eight sweeps in the executable
reference are therefore not an analysis timeout.

Targets accumulate over all intermediate deliveries. The proof does not
recompute control only from final DATA or remove a Target after a later
NORMAL packet. A finite run-31 capture is diagnostic; it is not used to
prove recurrence.

## 5. FL+1 is not relaxed

The proof checks Empty E in every cold state and in every later F/B state:
rows, saved records, submitted domains, current relations and replies.
For every such offered fact, generic C2 legality gives:

```text
FL(initial) <= globalLimit
FL(initial) <= FL(Dc)+1
```

The current NORMAL-MUST/real-E exception cannot apply: the first actual is
EXACT and every actual has Empty E. The same-head E repair is also idle.
The complete steady prepared families, including child queries, are checked
against both input caps for every budget n+8. No deeper selector budget is
borrowed for the broad row.
No exception is disabled, widened or added for this search. Paired output
intersection and `min(globalLimit,FL(Dp)+1)` cuts are unchanged.

Both the exact input's FL=2 and the deep condition's FL=3 fit every steady
global budget. The recurring base Dc is still at FL=0 and admits a start
only at FL=1. A larger global limit does not force the independent broad
question to advance. The fine query advances; the coarse query is renewed.

This counterexample does **not** select an EXACT-input exception or general
full-depth admission. Such a change could affect common cases and would
need a separate workload analysis and correctness design.

## 6. Why retained mechanisms do not remove it

- NE distinguishes real cuts. The critical root MAY is generated by an
  uncertain positive guard, rather than by cutting that result.
- Qualified heads and fine exact starts remain. Their NORMAL h results do
  not cover the independent root-MAY result.
- EXACT point transfer correctly rejects a read below the fine point.
  The coarse initial is STAR, so that point correction does not apply.
- Supported child delegation handles the selected correlated FLOW class.
  The fresh cross-mark T-to-U/U-to-T assignments are outside it.
- Saved MUST matching uses the definite lane. The recurring coarse records
  have STAR premises and are current DEMAND results.
- Identical definite reply support and whole-region NORMAL DATA coverage
  remain active. Neither can use a child region as a whole-root provider.
- Correlated FLOW subsumption cannot replace a mark-changing relation.
  There is no p-to-ret FLOW through the fresh result allocation.
- All protection memberships are plain. No protected/plain merge or
  cleaner survivor contributes to the recurrence.
- NORMAL reporting preserves the valid h observation but does not erase
  the separate anonymous DemandTarget or its next-run permission.

No analyzer repair is selected in this report. Earlier checked resolutions
remain valid; this is a new open case for the consolidated proposal.

## 7. Validation and scope

The package audits **166 new constructive claims; 5,160 claims in 259
source-hash-checked modules**. Only `propext` and `Quot.sound` are permitted
in theorem axiom closures. There are no custom assumptions, holes,
classical choice or external decision oracles. Exported values propose
witnesses; Lean's kernel checks their transitions and arbitrary-budget
recurrence.

**22 native tests pass**: two new full-program/component controls, eleven
current head-admission controls and nine same-head-E controls. The new
component test checks the precise-point guard rejection, coarse GEN result,
application of that conditional summary to the real point, and failure of
NORMAL child coverage over root MAY.

The unchanged native diagnostic completes **run-31/POLICY**, with a root
DemandTarget in every completed run and NORMAL report count 0. The proposed
reference retains a NORMAL observation from run-3. The native engine does
not implement the full consolidated NE/admission/coverage proposal. This
report claims no whole-engine bisimulation or equal report counts. The
uncapped theorem is for the stated complete marked-return/control model;
ordinary transfer/application components are checked directly in native
tests. JVM types, alias analysis and the complete IR are outside that model.

```bash
python3 spec/lean/proposals/exact-input-guard-cycle-20261116/check.py \
  --out /tmp/exact-input-guard-proofs

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ExactInputGuardCycleTest \
  --tests org.opentaint.dataflow.bidi.ExcludedHeadAdmissionTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest --console=plain
```

Production and old proof sources are unchanged. Bulk output and compiled
objects stay outside the repository. The complete readable trace is embedded
in the linked trace document; current receipt locations are in the package
README. Latest finite reference and native capture: **run-31**. The formal
recurrence has no iteration limit.

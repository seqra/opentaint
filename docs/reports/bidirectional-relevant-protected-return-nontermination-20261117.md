# Protected relevant returns: an uncapped demand cycle

17 November 2026. Synthetic data-flow reachability. FULL marks.
Follow [proof-guide.md](../../spec/proof-guide.md). Production is unchanged.
[Consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md).

**Historical counterexample, now repaired.** The
[same-flag delivery repair](../design/bidirectional-flag-aware-reply-service-20261117.md)
now stops this reference at **run-5**, retaining its NORMAL observation.
[Updated complete trace](bidirectional-flag-aware-reply-service-trace-20261117.md).
The old uncapped proof below shows why that repair is needed. Production is unchanged.

**Before that repair, the selected approach has a termination counterexample.**
Two positive marking rules on a fresh result are enough. Every generated
return has the existing protected membership H=1. The current reply-pruning
rules select only plain replies. Relevant protected returns also veto the
new terminal-service certificate. Full NORMAL-layer closure becomes ready;
the latest repair is enabled and does not close this case.

The complete reference states repeat **run-9/run-10 forever**, with
**41/47 helper DATA demand rows**, six retained NORMAL records and live
ZERO/Target routing. A NORMAL observation remains from **run-5**. No iteration
limit or within-run timeout is used to prove nontermination.

[Complete per-block fact trace](bidirectional-relevant-protected-return-trace-20261117.md)
puts forward demands, submitted facts and initials above each body, and
published summaries below it. Backward runs use the reverse placement.
The trace contains the full cold prefix through run-10.

## 1. Code and rules

```java
class Box { Box f; Box g; Box h; }

// Entry marking rule: assign T only at a.f.g.$.
void root(Box a) {
    Box x = make(a).h;
    Box y = make(x).h;
    Box z = make(y).h;
    // Observation rule: CM(z.M,T).
}

Box make(Box p) {
    Box r = new Box();
    // Positive marking rules at this point:
    // CM(p.f.g.g.M,T) => assign T to r.h.MUST.
    // CM(p.M,T)       => assign T to r.h.h.MUST.
    return r;
}
```

`$` = EXACT; `*` = correlated STAR; M = MAY; NE = nonempty MAY;
MUST = uniform taint. N/D are NORMAL/DEMAND. H=1 is protected, H=0 is plain.
All field exclusions E and mark exclusions mx are empty. There is one mark T.

The call graph is root -> make, with three sequential call sites. Both
CFGs are acyclic. Allocation, return and `.h` reads are ordinary analyzed
instructions. No loop, recursion, cleaner, configured pass, unresolved
library model, predefined summary, static field or field overwrite is used.

These rules assign T to fresh result positions. They do not copy an input
suffix or return the input object. They are not identity assignments or
special pass rules. The selected source rule checks protection against the
triggering conclusion mark: assigning T after a T trigger sets H=1.
This does not demote a NORMAL result to DEMAND.

## 2. The repeating route

The precise actual and its already owned query have:

```text
actual / initial: p.f.g.$/T,N,H=0
true return:     ret.h.h.MUST/T,N,H=1
ordinary h read: x.h.MUST/T,N,H=1
```

The exact point p.f.g.$ cannot satisfy CM(p.f.g.g.M,T). The root-mark check
is satisfied, and generates the protected NORMAL h.h result. Its whole
NORMAL service is admitted and applied. At field limits >= 2, the full
NORMAL-layer body closure succeeds with H preserved.

The same prepared demand family also retains the coarse query:

```text
initial:                   p.f.*/T,D
unknown deep check:        CM(p.f.g.g.M,T) may hold
published current summary: p.f.*/T -> ret.h.M/T,D,H=1
native call application:   ret.h.M/T,D,H=1
ordinary h read:           x.M/T,D,H=1
```

A STAR read beyond the known prefix loses precision, as specified. The
resulting M is not a real field cut. More global field room does not change
this step. The following calls repeat the same route at y and z.

The precise x.h.MUST/T,N,H=1 does not cover x.M/T,D,H=1: the latter also
admits the root and other descendants. MAY/MUST canonicalization and actual
NORMAL uniform coverage cannot remove that whole root-MAY membership.
No p-to-ret FLOW provider exists: the result is fresh, and only marking
rules connect the input mark to it.

The latest completion rules also leave it:

```text
suppress / suppressMark / suppressReply:
    require a plain current DEMAND reply
    current reply H=1                         => keep

full NORMAL-layer closure for p.f.g.$/T:
    true; ret.h.h.MUST/T is NORMAL, with H=1 preserved

reply-specific plain terminal service:
    ret.h.h.MUST/T,H=1 overlaps ret.h.M/T
    a relevant protected return is a veto     => no certificate
```

This is not the previous unrelated-k problem. The protected return is now
relevant. The proposed layer-aware fix expressly retains this veto and never
selects a protected current reply for pruning. No guard is disabled here.

## 3. Exact demand recurrence

One recurring forward edge is:

```text
X: p.f.*/T -> ret.h.M/T,DEMAND,H=1
```

After every forward run 2n+9, its handoff contains the paired backward row:

```text
Dc = ret.h.M/T
Dp = p.f.*/T
```

After every backward run 2n+10, the handoff again contains:

```text
Dc = p.M/T
Dp = ret.h.*/T
```

Thus the next forward run admits the same root/first-field queries. The
forward coarse marked output reaches the observation as DemandTarget; the
backward route reaches the entry marking rule and renews its permission.
The full stable states, not just these two representative rows, repeat.

| Run | Direction | Field limit | Helper DATA demand rows | Retained NORMAL records | Current full-closure keys | Root control |
|---|---|---:|---:|---:|---:|---|
| run-1 | forward | 1 | 2 | 0 | 0 | DemandTarget |
| run-2 | backward | 1 | 3 | 0 | 0 | entry permission |
| run-3 | forward | 2 | 8 | 1 | 1 | DemandTarget |
| run-4 | backward | 3 | 22 | 1 | 0 | entry permission |
| run-5 | forward | 4 | 23 | 6 | 2 | NORMAL observation + DemandTarget |
| run-6 | backward | 5 | 38 | 6 | 0 | entry permission |
| run-7 | forward | 6 | 39 | 6 | 2 | NORMAL observation + DemandTarget |
| run-8 | backward | 7 | 47 | 6 | 0 | entry permission |
| run-9 | forward | 8 | 41 | 6 | 2 | NORMAL observation + DemandTarget |
| run-10 | backward | 9 | 47 | 6 | 0 | entry permission |
| run-(2n+9) | forward | 2n+8 | 41 | 6 | 2 | same complete forward state |
| run-(2n+10) | backward | 2n+9 | 47 | 6 | 0 | same complete backward state |

Targets accumulate from every within-run delivery. The proof does not
cancel an earlier DemandTarget because a later NORMAL result exists.
Whole/mark completion flags stay empty; current NORMAL-layer closure has
two keys in every stable forward run.

## 4. Constructive nontermination proof

[Lean proof package](../../spec/lean/proposals/relevant-protected-return-cycle-20261117/README.md)
checks:

```text
F = complete run-9 state
B = complete run-10 state

history(9)  = F
history(10) = B

forall n >= 0:
    step(run=2n+9,  globalLimit=2n+8, B) = F
    step(run=2n+10, globalLimit=2n+9, F) = B

therefore forall n >= 0:
    history(2n+9)  = F
    history(2n+10) = B
```

Cold transitions, including the special run-1 and run-2 policies, are kernel
checked. Symbolic-limit checks establish every delivery/publication stage
for arbitrary additional field room; run-number regularity then gives the
induction. F has nonempty demand and a live DemandTarget; B renews entry
permission. Earlier forward runs do not satisfy the stopping predicate.
The schedule can never stop naturally.

Both within-run worklists reach exact fixed points. The model's eight-round
evaluator is sufficient and is not the reason for repetition. These checks
include the final complete raw state, all current summaries, saved NORMAL
replay, C2 children, C5 intersections and completion metadata.

All ordinary global, FL(Dc)+1 entry and FL(Dp)+1 output limits stay in force.
Every steady prepared initial and output has a checked bound. E is empty,
so the previously selected deeper NORMAL-MUST/real-hole exception never
activates. There is no new exception, suffix evidence, widened query,
protection erasure, arbitrary seed or raw-summary archive.

## 5. Validation and limits

The audit passes **176 new constructive claims; 6,455 cumulative claims
in 333 source-hash-checked modules**. Only `propext` and `Quot.sound`
occur as allowed foundational axioms; no classical choice or custom axiom is used.
Every analyzer definition is source-compared with the latest LayerBody.
Only the analyzed rules, their reverse transfer, the one-mark rule set and
observation mark differ. `bodyClosed` still uses `LayerCore.normalLayer`;
`suppressReply` still uses the new `LayerCore.completeFor`.

The three new native tests and eight retained layer-aware controls pass.
The unchanged full-program diagnostic reaches **run-31/POLICY**, with zero
NORMAL reports. The proposal reference retains a NORMAL observation from
run-5. As in the preceding reports, this inherited model/native difference
prevents inferring whole-engine equivalence or complete proposal integration.
The native finite run is a diagnostic, not the uncapped proof.

The generic conditional observation-preservation theorem is not refuted.
This counterexample concerns termination under the selected executable
completion eligibility and current-reply rules. The linked same-flag repair resolves this example without changing the historical proof. Production is unchanged.

Full captures, compiled proofs, audit receipts and test XML remain outside
the repository under
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/relevant-protected-return-cycle-20261117/`.

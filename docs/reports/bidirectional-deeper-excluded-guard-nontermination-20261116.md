# A deeper real field hole still renews demand

16 November 2026. Synthetic data-flow reachability. FULL marks. Follow
[proof-guide.md](../../spec/proof-guide.md). Production is unchanged.

**Historical policy:** this report keeps the policy before the narrowly
enumerated NORMAL MUST input-head exception. The [current repair](bidirectional-excluded-head-admission-20261116.md)
retains the actual head together with its real E only in a forward FULL
concrete MAY/NE family. Its reference naturally stops at **run-5**, preserves
the NORMAL observation, and retains all old-case results, latest **run-15**.
The global cap and all paired Dp+1 output caps stay mandatory. Production
remains unchanged; its finite diagnostic below still completes **run-31**.

**Historical result:** the preceding [consolidated approach](../design/bidirectional-demand-termination-approach-20261115.md)
had an uncapped counterexample. The complete marked-return/control reference
repeats its **run-9/run-10** states forever, with **73 forward / 83 backward
qualified demand rows** and a live root DemandTarget. The carried-real-E
repair is enabled. Each run reaches its own fixed point. The proof covers
arbitrarily increasing field limits, not a hard iteration cutoff.

The native diagnostic completes **run-31** and retains its DemandTarget.
That finite unchanged-engine result supports the example; it is not the
proof of uncapped nontermination or an integrated execution of all proposals.

## 1. Code and rules

```java
class Box { Box f; Box g; Box h; }

// Entry marking rule: assign T to a.f.g.MUST.
void root(Box a) {
    a.f.g.g = new Box();
    Box x = make(a);
    Box y = make(x);
    Box z = make(y);
    // Observation rule: CM(z.M,U).
}

Box make(Box p) {
    Box r = new Box();
    // Four ordinary marking rules at this point:
    // CM(p.f.g.g.M,T) => assign U to r.MUST.
    // CM(p.M,T)       => assign U to r.h.MUST.
    // CM(p.f.g.g.M,U) => assign T to r.MUST.
    // CM(p.M,U)       => assign T to r.h.MUST.
    return r;
}
```

All three calls share the same analyzed make owner. Both bodies and the
call graph are acyclic. Every configured action assigns a literal full
mark to a fresh result. There is no loop, recursion, cleaner, pass rule,
unresolved method, intrinsic-MAY action or exceptional control flow.

The field replacement is ordinary code. Its parallel keep transfers create
the real field exclusion. They are not configured pass rules. The source
result is subject to the normal field cut before it reaches that write.

Relative to the previous repaired example, the program moves the marked
head from a.f to a.f.g, the replacement from a.f.g to a.f.g.g, and the deep
conditions from p.f.g to p.f.g.g. The h outputs stay unchanged. The analyzer
rules stay unchanged.

## 2. The decisive admission boundary

Notation: `$`=EXACT, `*`=correlated STAR, M=MAY, NE=nonempty MAY,
MUST=uniform, N/D=layer, E=real field exclusion. All H memberships are plain.
`[Dc | Dp]` is one entry selector with its original paired output selector.

Once the field budget represents the source head, the ordinary replacement
produces:

```text
before: a.f.g.MUST/T {}, NORMAL
write:  a.f.g.g = new Box()
after:  a.f.g.MUST/T {g}, NORMAL
```

Take a repeated row `[p.M/T | ret.*/U]`:

```text
submitted:              p.f.g.MUST/T {g}, NORMAL
first-field initial:    p.f.*/T {}, DEMAND
existing FLOW companion:p.f.*/FLOW {}, NORMAL
existing prefix probe:  p.$/FLOW {}, NORMAL
fine qualified query:   p.f.g.MUST/T {g}, NORMAL
```

The new same-head E rule **does not change** the first-field initial. Its
head p.f differs from the actual head p.f.g. Moving `{g}` to p.f would mean
excluding p.f.g, which includes the actual's own marked root. The selected
rule correctly prohibits that shift. The fine query keeps the real hole.

The resulting rule transfers are:

```text
coarse p.f.*/T {},D:
    CM(p.f.g.g.M,T) may hold -> ret.M/U,D
    CM(p.M,T) may hold     -> ret.h.MUST/U,D

fine p.f.g.MUST/T {g},N:
    CM(p.f.g.g.M,T) cannot hold -> no root result
    CM(p.M,T) holds            -> ret.h.MUST/U,N
```

The admitted coarse summary can apply to the actual p.f.g region. It emits
root MAY/U on DEMAND at x. The ready NORMAL replies stay under x.h. Whole
region coverage correctly cannot use that child to remove root MAY.

The following calls maintain both routes:

```text
coarse: a.f.g.MUST/T {g},N -> x.M/U,D -> y.M/T,D -> z.M/U,D
normal: same actual       -> x.h.MUST/U,N
                              -> y.h.MUST/T,N -> z.h.MUST/U,N
```

The NORMAL route also has exact h images from paired C5. They remain
available and are not absorbed into the uniform query during admission.
They do not cover the unrelated whole-root MAY region. The observation has
a valid NORMAL witness from run-5 onward and an independent DEMAND witness.
The NORMAL report does not cancel the already emitted DemandTarget.

## 3. Per-run trace

The [complete annotated trace](bidirectional-deeper-excluded-guard-trace-20261116.md)
lists all demand rows, submitted facts, emitted initials and admitted
NORMAL/DEMAND summaries for **both analyzable blocks**, root and make, in
every run from run-1 through run-10. It uses the variables from the code.
Forward inputs are above each declaration and summaries below its end;
backward placement is reversed. Several output selectors on one line mean
separate paired rows, not a new combined selector.

The counts below are for the marked-return/control reference, not all engine
facts. A finite capture is also available through **run-31**.

| Completed run | Direction / field limit | Qualified rows | Retained NORMAL return records | Root DemandTarget / backward permission | NORMAL observation retained |
|---|---|---:|---:|---|---|
| run-1 | F / 1 | 4 | 0 | Target | no |
| run-2 | B / 1 | 14 | 0 | permission renewed | no |
| run-3 | F / 2 | 24 | 0 | Target | no |
| run-4 | B / 3 | 38 | 0 | permission renewed | no |
| run-5 | F / 4 | 40 | 6 | Target | yes |
| run-6 | B / 5 | 61 | 6 | permission renewed | yes |
| run-7 | F / 6 | 64 | 12 | Target | yes |
| run-8 | B / 7 | 83 | 12 | permission renewed | yes |
| run-9 | F / 8 | 73 | 12 | Target | yes |
| run-10 | B / 9 | 83 | 12 | permission renewed | yes |
| run-(9+2n) | F / (8+2n) | 73 | 12 | Target | yes |
| run-(10+2n) | B / (9+2n) | 83 | 12 | permission renewed | yes |

Run-1 truncates the two-field source head to a.f.NE/T,D. The write's native
parallel keeps can emit this same scalar value twice; ordinary packet and
domain deduplication removes that duplication. It is not the repeating
iteration pattern. All real cuts, including this one, use NE.

Run-2 starts reverse EXACT/STAR result queries and creates both the qualified
f.NE and the broad M input questions. Run-3's field limit fits the source
head, but its restricted input questions still have coarse first-field
starts. Later backward runs add the deeper qualified questions; run-5 can
retain the first six NORMAL h records. The coarse base starts remain legal.

At the steady forward boundary, repeated rows include:

```text
[ret.M/U | p.*/T]       and [ret.M/T | p.*/U]
[ret.M/U | p.f.*/T]     and [ret.M/T | p.f.*/U]
```

The corresponding steady backward rows include:

```text
[p.M/T | ret.*/U]       and [p.M/U | ret.*/T]
```

Backward broad result queries intersect the r.h assignments and request
their broad p.M operands. These renew the same row family. In root, the
backward demand traverses the three calls and the real replacement, reaches
the entry marking rule, and renews source permission for the next forward
run. These facts are derived from the calls; they are not assumed as an
external recurring input packet.

## 4. Constructive uncapped proof

Let F be the complete frozen state after run-9 and B the state after run-10.
They contain qualified demand, retained NORMAL records, actual domains,
current C5-admitted summaries, actual reply packets and control state.

The [Lean package](../../spec/lean/proposals/deeper-excluded-guard-cycle-20261116/README.md)
constructs their cold prefix and proves:

```text
forall n >= 0:
    State(9+2n)  = F
    State(10+2n) = B

F.rows has 73 members; B.rows has 83 members.
F.saved = B.saved; there are 12 retained NORMAL return records.
F.report = true; F.observationActive = true; B.sourceAllowed = true.

forall n >= 0:
    [ret.M/flip(m) | p.*/m] belongs to State(9+2n).rows
    [p.M/m | ret.*/flip(m)] belongs to State(10+2n).rows
```

Here m ranges over the literal marks T and U. The row families are concrete
witnesses. Membership is proved in the **qualified** refinement view even
when another executable packet representation is smaller.

The proof has four steps:

1. Check each cold transition from run-1 through run-10 and one further
   complete within-run sweep at each result. The latter proves quiescence.
2. After the special first runs, factor out direction and field budget.
   Keep the new carried-E gate enabled in this phase equivalence.
3. For **every budget n+8**, check each delivery/publication stage of the
   forward transition B to F and backward transition F to B. Check another
   complete sweep at both steady results. Targets accumulate across all
   intermediate deliveries.
4. Instantiate those parametric transitions at limits 8+2n and 9+2n and
   induct on the number of forward/backward pairs. No later forward stop
   test succeeds; no earlier forward stop was skipped in the cold prefix.

The model's eight worklist sweeps are therefore not an analysis timeout.
The proof shows they have already reached a fixed point. Neither run-11 nor
the native run-31 diagnostic is used as a redundancy argument. Increasing
the limit indefinitely preserves the two exact states.

## 5. Why the selected mechanisms do not close this case

| Selected mechanism | Why it does not remove this recurrence |
|---|---|
| NE on every real cut | The decisive root-MAY output is regenerated by an uncertain guard; it is not itself a field cut |
| Bounded first-field refinement | A p.M question still starts at p.f when the actual head is p.f.g; it does not select the whole chain |
| Preserve same-head real E | Correctly applies to p.f.g, but cannot shift that E to the distinct head p.f |
| Retain qualified deeper questions | Fine questions disprove the deep guard; they do not cancel the independent base query |
| Child routing for supported FLOW transfers | Fresh T-to-U/U-to-T GEN is outside that correlated FLOW class |
| Strict saved MUST replay | Enabled; the repeating row has a STAR premise, not an unsupported saved MUST premise |
| Identical EXACT/MUST support and actual uniform coverage | NORMAL h output cannot cover whole-root MAY |
| NORMAL FLOW subsumption | A diagonal FLOW provider cannot replace a cross-mark generated relation |
| Literal protection | Plain throughout; no protected/plain merge is involved |
| Accumulating Target policy | A valid NORMAL observation does not erase the separate DEMAND witness |
| Larger global limits | The base Dc has FL=0 and still requests a bounded first-field start; the old coarse result remains legal |

This report selects no repair and weakens none of these guards. In particular,
copying the child's `{g}` onto p.f would discard an actual allowed region.
Dropping the coarse query or its Target just because a NORMAL h observation
also exists would need a separate complete-service proof.

## 6. Validation and model scope

The new package checks **160 constructive claims; 4,502 audited claims across
218 source-hash-checked modules**. The axiom audit allows only `propext` and
`Quot.sound`. There are no custom assumptions, holes, classical choice or
external decision oracles. Exported states propose witnesses; Lean checks
their equalities and the parametric recurrence in its kernel.

**11 native tests pass**: two new program/component controls and nine
carried-E adapter controls. The component test verifies that an ordinary
replacement creates p.f.g.MUST/T {g}, that the latest same-head map leaves
the shorter p.f STAR query unchanged, that the fine guard is blocked, and
that the coarse guard still produces root MAY/DEMAND.

The unchanged native driver completes **run-31**, reason POLICY, with its
root DemandTarget in every completed run. Its NORMAL report count is zero;
the proposed reference retains a NORMAL observation from run-5. The engine
does not implement the entire consolidated NE/admission/coverage proposal.
Do not claim a whole-engine bisimulation, equal counts or a native proof of
the proposed recurrence. The ordinary transfer components are checked
directly; native finite diagnostics and the constructive reference proof
are separate evidence.

All new reference code is the previous carried-E example model with the
program's source/guard/write paths changed, plus the required source cut
before the deeper replacement. The emitter, real-E map, raw C5, complete
paired restriction, first-field plan, strict saved MUST lane, actual DATA
coverage and accumulating Targets are reused unchanged. No production file
or old proof source is modified. The ordinary root/make blocks have no CFG
loop decomposition; aliases and the full IR are outside this reference.

```bash
python3 spec/lean/proposals/deeper-excluded-guard-cycle-20261116/check.py \
  --out /tmp/deeper-excluded-guard-proofs

cd core
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DeeperExcludedGuardCycleTest \
  --tests org.opentaint.dataflow.bidi.ConcreteQueryExclusionsTest --console=plain
```

Bulk exports, compiled objects, receipts and logs stay outside the repository.
The complete readable per-run trace is embedded in the linked trace document.
The catalogue and consolidated approach now identify this case as open.

# Soundness investigation after possible DIRECT replay

17 November 2026. Synthetic data-flow reachability. FULL mode.
Production HEAD: `966a40c36472`. Production is unchanged.
[Consolidated proposal](../design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../spec/proof-guide.md).

**No additional soundness counterexample was found in the checked scope.**
The expanded reference checks complete naturally through **run-11**. Nine
new cold native controls complete through **run-9**. The combined targeted
native suite passes **92 tests**. Earlier reference cases still have their
separate bounds, including run-17; this report does not replace them.

This result does not close the general G1–G4 obligations. It selects no
new analyzer behavior. R34 remains the latest semantic repair: a possible
DIRECT read returns DEMAND, while its saved NORMAL record keeps its real
direction. Field limits and initial-emission rules are unchanged.

## 1. Expanded checks

The previous R34 search checked a broad observation. This search also
selects exact observation locations and changes the backward question to
that location. Checking more output locations after a broad-only run would
not be sufficient: a different observation changes demand.

| Reference screen | Configurations | Main additions | Mismatches | Unfinished within-run fixed points | Latest natural run |
|---|---:|---|---:|---:|---|
| Prefix controls | 384 | EXACT or MUST input, one/two calls, empty/nonempty read and write prefixes | 0 | 0 | run-7 |
| Branch and observation | 5,660 | Two return branches; exact positive and negative observation locations | 0 | 0 | run-7 |
| Three owners | 5,258 | Outer wrapper, inner wrapper and helper; two independent prefix changes | 0 | 0 | run-11 |
| Ordinary writes | 2,302 | Root and nested strong writes, real E, return reads, alternative branches | 0 | 0 | run-7 |
| Total | 13,604 | Screens overlap; this is a configuration count | 0 | 0 | run-11 |

Every configuration reaches the checked empty frontier. The scans allow
run-25 for the first two screens and run-33 for the other screens. Within a
run, the scanner requires the actual reference fixed point; 60 rounds is a
diagnostic ceiling, not a proof that unfinished work can be discarded.
No ceiling was reached. The hard run-11 production limit is not used to
classify an edge as redundant or a configuration as complete.

The field alphabet is f/g. Source heads are `.`, `.f`, `.g`, `.f.g`, `.g.f`
and `.g.g`, with EXACT or MUST tails and Empty E. Wrappers use the prefix
pairs `(.,.)`, `(g,g)`, `(g.g,g.g)` and `(f,g.f)`. Helper prefix pairs are
`(f,f)`, `(f.g,f)`, `(g,g.f)` and `(.,f)`. The branch screen uses ordered
pairs from that helper set. The three-owner screen adds another wrapper.
Each program makes one or two outer calls.

For each program, exact observation paths include up to two locations from
the unbounded expected output, plus `.`, `.f` and `.g`, with duplicates
removed. Uniform regions supply concrete descendant probes. The overwrite
screen uses seven small bodies, including `p.f=new`, `p.f.g=new`, reads
from those objects, fresh return-prefix construction and two return branches.
The executable sources contain the complete finite case generators.

Expected results come from uncapped ordinary AP return execution. The
restricted execution keeps current C2, prepared child routing, paired C5,
normalization, real E, NE cuts, saved replay and R34. It must preserve the
observation and must not create a NORMAL observation absent from that
uncapped reference. The tests do not claim an independent JVM semantics
proof for the shared AP primitives.

## 2. First rejected candidate: empty DATA demand

An initial check stopped when return-DATA demand was empty. This produced
apparent losses. That test was incomplete: a cut call result can still
produce DemandTarget in the caller. The corrected harness includes this
existing continuation condition; it adds no analyzer rule.

```java
void main() {
    Node x = new Node();
    markTAtF(x);                // x.f.$/T,N
    Node y = wrap(x);
    observeBelow(y);            // CM(y.MAY,T)
}
Node wrap(Node x) { return pack(x); }
Node pack(Node x) {
    Node y = new Node(); y.f = x;
    return y;
}
```

```text
run-1, limit 1:
    pack NORMAL summary: x.*/FLOW -> ret.f.*/FLOW
    wrap NORMAL summary: x.*/FLOW -> ret.f.*/FLOW
    no return-DATA demand in either owner
    original actual x.f.$/T,N
    normal summary application gives y.f.f.$/T,N
    global cut gives y.f.NE/T,D
    observation emits ZERO -> DemandTarget,D
    => do not stop

run-2, limit 1:
    retained NORMAL service carries the backward question to the source
    no need to reanalyze pack merely to replay that service

run-3, limit 2:
    saved NORMAL application gives y.f.f.$/T,N without a cut
    observation emits the NORMAL target
    no remaining refinement demand; natural completion
```

The reference proves the run-1 distinction and the NORMAL run-3 result.
A new unmodified native control checks that the helper's run-1 summaries
are NORMAL, the caller retains DemandTarget, and the finding is NORMAL at
natural **run-3**. The native test uses one call to pack; the reference also
keeps the transparent wrap owner. Production still uses MAY at a real cut;
the proposal uses NE. Both are provisional and need Target continuation.

The reference uses this bounded outer-control check:

```text
observationDemand = any offered DEMAND result that can reach this observation
emptyFrontier     = empty return-DATA demand AND NOT observationDemand
```

It does not treat an arbitrary offered fact as a Target, and it does not
introduce a new keepalive mechanism in the engine. The actual typed Target
and source-permission machinery remains a native responsibility.

## 3. Second rejected candidate: a stronger MUST initial

A possible concern was that a deeper uniform input starts a stronger
uniform query at its shorter prefix. The current selected C2 does not do
that in the Empty-E first-field case:

```text
demand:     p.MAY/T
submitted:  p.f.g.MUST/T,N

initials:
    p.f.*/T,D
    p.f.*/FLOW,N            // existing conditional companion
    p.$/FLOW,N              // existing conditional prefix probe

NOT emitted: p.f.MUST/T,N
```

Thus the retained relation does not claim uniform T at p.f merely because
T is uniform at p.f.g. The dedicated MUST query is available at its own
admitted head. The separate, already selected real-hole exception retains
the actual head; it does not justify a stronger shortened MUST hypothesis.

The following native controls exercise concrete rule actions:

```java
void main() {
    Node x = new Node();
    markTBelowFG(x);            // x.f.g.MUST/T,N when represented
    Node y = make(x);
    observeUAtRoot(y);          // CM(y.$,U)
}
Node make(Node p) {
    Node y = new Node();
    // Rule: CM(p.MAY,T) assigns U at y.$.
    return y;
}
```

The retained data guide progresses through p.f, then p.f.g. The first-field
starts remain STAR/DEMAND. A same-head p.f.g.MUST/T query can finally infer
and apply a NORMAL result. In this control, natural completion is run-7.
This rejects the attempted counterexample; it does not prove that every
possible future MUST service history is covered.

| Source head length | EXACT input, changed mark | MUST input, changed mark |
|---:|---|---|
| 1 | NORMAL observation, run-3 | NORMAL observation, run-5 |
| 2 | NORMAL observation, run-5 | NORMAL observation, run-7 |
| 3 | NORMAL observation, run-7 | NORMAL observation, run-9 |

Two further controls assign T instead of U. They retain the NORMAL
observation at run-5 for the two-field EXACT input and run-7 for the
corresponding MUST input. The ordinary same-mark protection rules remain
enabled. No special pass or cleaner rule is used.

## 4. Proof and native evidence

The [proof package](../../spec/lean/proposals/post-direct-soundness-audit-20261117/README.md)
adds **8 constructive claims**: **7,245 cumulative claims in 422 source-hash-
checked modules**. It proves:

- A pending observation DEMAND forbids the empty-frontier stop.
- The pack control has no return-DATA demand at run-1, but has a provisional
  observation result; it retains its NORMAL observation at run-3.
- An arbitrary deeper MUST actual uses STAR in the ordinary first-field C2
  policy. Current full-mark C2 cells preserve the DEMAND/companion layers.
- Same-head MUST keeps its definite lane; backward C2 does not start MUST.

The package executes all four finite generators and rejects an early exit,
a mismatch, an unfinished run or a warning. It audits transitive theorem
axioms, permitting only `propext` and `Quot.sound`. No classical choice,
custom axiom, proof hole or external decision oracle is used.

Nine new native cold tests join the previous 83-test suite: **92 pass**.
They use no prototype adapter and require natural `NO_DEMAND_EDGE`, with
one NORMAL observation and no provisional report. The older expected-broken
production prefix controls remain in that suite. The complete proposal,
including NE and R34, is still not installed in the production driver.

## 5. Scope that remains open

The expanded reference is a unary, ordinary return-cone model. It grants
fresh forward source inputs optimistically. Its outer observation check is
not the complete typed Target/source-permission state machine. A positive
result here can therefore hide a source-permission problem; a finite search
cannot close that gap. The native cold controls cover selected complete
histories, not the entire proposal.

The screens do not cover arbitrary ND rule joins, aliases, static protocols,
physical loop ports, all protected completion histories or all mark-changing
programs. Ordinary mark-changing and same-mark controls are checked natively,
not added to the neutral prefix model. The general obligations remain:

```text
G1  Every needed later execution has NORMAL service or adequate demand.
G2  Its certificate matches the complete native binding and effects.
G3  Every normalized NORMAL FLOW path has valid suffix lifting.
G4  Handoff, loop gates and stopping keep every needed guide.
```

There is no new confirmed concrete gap from this investigation. This is
not a whole-analyzer soundness or universal termination certificate. No
transfer, admission, matching, field limit or stopping policy changes are
selected by these results.

Reproduce the reference/proof check:

```bash
python3 spec/lean/proposals/post-direct-soundness-audit-20261117/check.py \
  --out /tmp/post-direct-soundness-proofs
```

Run the new native controls:

```bash
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.PostDirectSoundnessAuditTest --offline
```

Generators, essential traces and all result counts are in the repository.
Receipts, compiled modules, XML and logs are outside Git under the external
report-data policy.

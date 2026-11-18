# R37 [REC]: recursive Target repetition and confirmed root service

**Later correction:** R37's report-ID-only K is insufficient for the
marking-point/full-mark/observer contract. The
[R38 source-specific repair](../mark-origin-soundness-20261117/README.md) supersedes that predicate. Its generic
terminal OR proof and this single-origin recursive trace stay valid.
Do not apply this document's original ID-only retirement rule to multiple
unserved marking points. The repaired two-origin native wrapper completes
naturally at run-9; the single-origin case retains natural run-7.


17 November 2026. Constructive Lean **4.35.0**. Production is unchanged.
Follow [proof-guide.md](../../../proof-guide.md).
[Code, per-run annotations, complete rule and validation scope](../../../../docs/reports/bidirectional-recursive-target-termination-20261117.md).
[Consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md#confirmed-root-target-service-r37-rec).

## Models and claims

| Module | Claims | Scope |
|---|---:|---|
| `RecursiveWrapperCycle` | 27 | Ordinary recursive return construction; finite within-run cut fixed point; actual C2 prefix probe and C5 cap; opposite saved NORMAL read recreates root MAY; computed ZERO/Target recurrence for every uncapped pair |
| `TargetSupport` | 14 | Any finite terminal derivation through cyclic relays; false bit covers all origins; mixed/unknown fallback; conceptual origin union equals Boolean OR; at most two notifications per Target key; executable finite certificate validator |
| `RootTerminalRepair` | 9 | Existing root control policy plus R37; no early use of a new confirmation; DATA frontier retained at run-5; no root permission at run-6; natural run-7 and every later quiet state |
| `RecursiveSearch` | 2 | Independent negative query and correct same-head NE/MAY observation; executable fresh recursive search |

The checker audits **52 new claims** and revalidates the source hashes of
the **7,308-claim / 427-module** parent closure: **7,360 claims in 431
modules**. Transitive axioms may contain only `propext` and `Quot.sound`.
Classical choice, custom axioms, proof gaps and native decision shortcuts
are rejected. Existence witnesses are executable.

The recurrence proof is a constructive return-cone/control witness, not a
complete model of native packed storage or concurrent scheduling. It derives
the marked/cut return and backward permission, instead of assuming a repeated
Target. Finite native run-15 evidence is separate from the uncapped proof.

R37 is a **semantic handoff change**. It removes only forward root ZERO/DT
guidance whose complete origins already have retained NORMAL root reports.
It keeps anonymous Target keys, all current-run Target propagation and all
DATA guidance. It adds one monotone bit per Target key; no AP annotation,
new suffix evidence, full origin set or field-cap exception is selected.

The general certificate proves preservation of every current unconfirmed
terminal lineage. Whole-program no-loss also needs the existing AP
guidance-completeness invariant for later observations. G1–G4 remain open;
this package is not a new whole-analyzer termination or soundness proof.

## Fresh search

**11,340 configurations**, all with finite within-run fixed points and
natural completion; latest **run-13**. Direct wrapper words are f, g, ff,
fg. Mutual graphs pair those words and include with/without the second base
case: 36 graphs. EXACT source paths have depth 0..2. EXACT/MAY/NE observations
have depth 0..3. It reuses prepared C2, paired C5, saved-first, R32/R34 and
ordinary cuts; it keeps Target continuation and backward marking permission.
The total includes 7,560 configured-shape EXACT/MAY observation cases and
3,780 NE region-query components. No new serialized rule shape is selected.

The independent concrete oracle uses the nonempty periodic wrapper prefix.
For this linear family, any broad-prefix match has a witness by cycle count
`length(query)+1`; exact matches need no longer word. The search fails if a
run has no fixed point, if the observation differs from the oracle, or if
the analyzer does not stop within its scan window. A diagnostic bound is
never counted as successful termination.

The scope is one exact marking and one observation in a void root, with
neutral unary recursive return cones. No ND, aliases, statics, GROUP,
recursive cleaners or conditional marking integration is claimed. The
generic Target proof and native metadata controls separately cover cyclic,
mixed and unknown terminal origins. Earlier proof scopes are retained.

## Reproduce

Use an output directory outside Git under the [external data policy](../../../../docs/reports/EXTERNAL_DATA.md):

```bash
python3 spec/lean/proposals/recursive-target-service-20261117/check.py \
  --dependencies /path/to/uniform-cleaner-spine-20261117/checked-proofs \
  --out /path/to/recursive-target-service-20261117/checked-proofs
```

The parent must contain its receipt and source-identical compiled modules.
If absent, run the [parent checker](../uniform-cleaner-spine-20261117/check.py)
first. The checker compiles all four new sources in dependency order before
evaluation, audits each claim's axioms, then runs the fresh search. It
rejects stale parent source hashes, warnings, incomplete output and gaps.

Native controls and proposal adapters:

```bash
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.RecursiveWrapperTerminationTest \
  --tests org.opentaint.dataflow.bidi.RecursiveTargetSupportTest --offline
```

The **12 new tests**, plus the earlier **111**, all pass (**123 total**).
The current single recursive wrapper reaches **run-15/POLICY**, with a
NORMAL observation from **run-3**. The single-origin handoff adapter keeps
all DATA rows/records/seeds and finishes at natural **run-7** without an
iteration limit. The metadata model covers cycles, late true upgrades,
unknown producers, mixed origins, frozen epochs, key count and arrival
order. It does not change production Target storage.

Native mutual wrappers already complete naturally at **run-5**; the adapter
does not run there and does not claim credit for that stop. An unreachable
sibling observer remains absent at natural **run-3**. Production still
uses MAY at real cuts; the selected reference uses NE. These differences
are explicit and do not turn component tests into a whole-proposal run.

External artifacts under `recursive-target-service-20261117/` include the
cumulative proof receipt, per-claim axiom logs, search output, Gradle log,
source hashes and 123-test XML. There is no new project performance run.

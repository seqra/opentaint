# Same-head concrete queries retain real field exclusions

16 November 2026. Follow [proof-guide.md](../../../proof-guide.md).
[Rule, examples, traces and scope](../../../../docs/reports/bidirectional-concrete-query-exclusions-20261116.md).
Production is unchanged.

Restricted FULL concrete-demand C2 families copy real actual E onto an
existing Empty-E STAR start only at the identical base/path and only from
STAR/MUST actuals. The same map covers that family's FLOW companion. C5
checks the new complete raw image. No member, field, mark or layer is added.
Independent FLOW-only demand families, GROUP, run-1, empty actual E,
changed-head starts and the MUST lane keep their previous behavior.

## Checked results

**PASS: 458 new claims; 4,342 audited declarations in 210 modules**, Lean
4.35.0. Each theorem's axiom closure is checked; only `propext` and
`Quot.sound` are allowed. There are no custom axioms, holes, classical
choice or external evaluation oracles. Executable membership and existence
claims produce witnesses. Frozen states are checked by kernel reduction.

| Modules | Scope |
|---|---|
| CarryPolicy | New emitter and raw C5; old equivalence for run-1, FLOW-only rows and empty E |
| CarrySafety | Full point-region equality at an eligible head; no shifted/synthetic E; unchanged marks/layers/geometry/cardinality; grammar/budgets; constructive C5 offer witnesses |
| CarryNeutralPlan, CarryNeutral, CarryCampaign | Entire old pipeline/cold-step equivalence on FLOW-only demand rows, including actual nonempty E |
| CarryOld* (18 ordinary cases) | Check that condition at each complete cold prefix, preserve exact states/findings/stops, prove no restart at arbitrary later run numbers |
| CarryExcluded, CarryNewCold | New real-exclusion example from cold run-1 through the natural run-5 stop, per-run quiescence, NORMAL observation at run-3, no Target cancellation, uncapped quiet suffix |
| CarryAlternating, CarryOldAlternating | Previous alternating-generator example rerun with new admission; identical cold states and uncapped run-5 stop |
| CarryStrictExact, CarryStrictUniform, CarryStrictDifferent | Whole-history equality under their empty-E actual offers; strict saved MUST semantics unchanged; both observations and uncapped run-5 stops |
| CarryControls | Protected closure run-3; selected cleaner run-1; unchanged C5 conclusion bound |

The previous 18 cases stop at the same runs, latest **run-15**. The other
four concrete cases and the new case stop at **run-5**. Their references
accumulate every reached Target. A late NORMAL DATA result never removes
an earlier emitted control effect. The new example has six residual method
rows after run-3, no root DemandTarget, and an empty frontier after run-4.
The next forward run, run-5, stops normally.

This is a scoped termination proof for the supplied examples, not universal
termination or an integrated production scan. The historical parent package
still proves the old run-7/run-8 cycle; importing it does not transfer that
cycle to the repaired emitter. Real field E is kept in the existing key;
distinct actual E values may increase the number of conditional keys.

## Reproduction

From the repository root:

```bash
python3 spec/lean/proposals/concrete-query-exclusions-20261116/check.py \
  --out /tmp/concrete-query-exclusions-proofs
```

The default command first checks all parent models. To reuse a previous
checked parent build, give `--dependencies`; the checker verifies every
parent source hash before copying compiled dependencies:

```bash
python3 spec/lean/proposals/concrete-query-exclusions-20261116/check.py \
  --dependencies /drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/excluded-guard-cycle-20261116/proofs-final \
  --out /tmp/concrete-query-exclusions-proofs
```

Current receipt and all compiled/log output:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/concrete-query-exclusions-20261116/proofs-final/receipt.json
```

`scripts/demand_experiments/concrete-query-exclusions-20261116/Explore.lean`
exports finite diagnostic states from the executable new reference. With
`LEAN_PATH` set to the checked output, run `lean` on that file and redirect
its output outside the repository. Numeric encoding: base 0=p, 1=ret;
fields 1=f, 2=g, 3=h; marks 1=T, 2=U. The export is not the proof oracle.
Natural termination is proved independently for arbitrary later run numbers.

The [native adapter](../../../../core/opentaint-dataflow-core/opentaint-dataflow/src/test/kotlin/org/opentaint/dataflow/bidi/ConcreteQueryExclusionsTest.kt)
has nine passing tests. Together with the four previous component/control
classes, **31 tests pass**. See the report for the Gradle command. Latest
unchanged native diagnostic: **run-31**; no production NE integration is
claimed.

# NORMAL uniform actuals retain their excluded head

16 November 2026. Follow [proof-guide.md](../../../proof-guide.md).
[Full rule, exhaustive FL+1 cases, traces and costs](../../../../docs/reports/bidirectional-excluded-head-admission-20261116.md).
Production is unchanged.

Restricted **forward FULL concrete MAY/NE** families may replace an existing
shorter Empty-E STAR start with the **NORMAL MUST actual's** existing
head and nonempty real E. Its existing FLOW companion follows the same map.
No extra initial is emitted. STAR actuals, DEMAND actuals, backward runs,
FLOW-only demands, GROUP and failed ordinary admission are not exceptions.
The previous same-head E rule remains selected.

This is a major relaxation of the external **entry** FL(Dc)+1 cap in one
enumerated class. The actual and new start remain globally bounded. The
paired **output** FL(Dp)+1 cap has no new exception. C5 uses the new complete
raw C2 image before normalization, without an actual-input history cache.

## Results

**492 new constructive claims; 4,994 audited declarations in 251 modules**,
Lean 4.35.0. Only `propext` and `Quot.sound` are permitted in axiom closures.
No custom axioms, holes, classical choice or external proof oracle is used.
Frozen states are executable witnesses checked by kernel reduction.

- Deep and shallow real-hole cases: natural **run-5** stops, valid NORMAL
  observations, accumulating Targets and uncapped quiet suffixes.
- Eighteen old ordinary cases: exact histories unchanged, latest **run-15**.
- Alternating-generator and three strict concrete-replay cases: **run-5**,
  with their observations and uncapped no-revival results.
- Protected and selected-cleaner controls: separate **run-3/run-1** results.
- Native component/control suite: **41 passing tests**, including eleven new
  adapter tests. Historical unchanged diagnostics still complete **run-31**.

This is not universal termination, an integrated production execution or
a proof that the exception is rare in project workloads. Distinct already
arrived heads may split a formerly shared query key. The report gives the
required frequency, overrun and workload measurements before activation.

## Modules

| Module family | Proof scope |
|---|---|
| HeadPolicy | Narrow mapping, actual-tail/layer/direction exclusions, exact old behavior for FLOW/empty E/run-1 |
| HeadSafety | Executable old-member witnesses, same family size, exact actual point-region preservation, no synthetic path/E, no new tail, mandatory global bound, unchanged precise selectors, raw C5 witnesses, exhaustive over-Dc+1 exception certificate |
| HeadNeutralPlan, HeadNeutral, HeadCampaign | Generic whole-pipeline equality with the old ordinary engine on FLOW-only rows |
| HeadOld* (18 ordinary cases) | Verify that condition at each cold prefix, preserve exact states and no-revival at arbitrary later run numbers |
| HeadDeep, HeadDeepCold | Latest deeper-hole program from cold run-1 through natural stop run-5, fixed points and uncapped quiet state |
| HeadShallow, HeadShallowCold | Previous hole program checked under the same new policy; stop run-5 preserved |
| HeadAlternating, HeadOldAlternating | Full prior alternating cold states and accumulated Target behavior preserved |
| HeadStrictExact, HeadStrictUniform, HeadStrictDifferent | Whole-history equality under empty-E offers; strict saved MUST policy retained |
| HeadControls | Selected protected/cleaner results; every admitted C5 conclusion stays within its original paired output bound |

The imported historical parent still proves the old run-9/run-10 cycle.
It is a dependency, not a recurrence of the repaired machine. No old proof
source or production transfer is modified. The scalar reference does not
implement JVM types, aliases, real CFG ports or all native rule forms.

## Reproduce

```bash
python3 spec/lean/proposals/excluded-head-admission-20261116/check.py \
  --out /tmp/excluded-head-admission-proofs
```

The default builds all parents. To reuse a checked parent output, with every
source hash verified first:

```bash
python3 spec/lean/proposals/excluded-head-admission-20261116/check.py \
  --dependencies /drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/deeper-excluded-guard-cycle-20261116/proofs-final \
  --out /tmp/excluded-head-admission-proofs
```

Current restricted-policy receipt:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/excluded-head-admission-20261116/proofs-restricted-final/receipt.json
```

The sibling `scripts/demand_experiments/excluded-head-admission-20261116`
directory contains deep/shallow finite exporters and a trace renderer.
Set LEAN_PATH to the checked output, run `lean` on the selected exporter,
and redirect logs outside the repository. Its finite run-31 export is
diagnostic only; kernel proofs establish uncapped no-revival. Encoding:
base 0=p, 1=ret; fields 1=f, 2=g, 3=h; marks 1=T, 2=U.

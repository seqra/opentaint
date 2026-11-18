# Unadmitted NORMAL return: uncapped counterexample

Constructive Lean 4.35.0. Synthetic data-flow reachability; production unchanged.
[Explanation and code](../../../../docs/reports/bidirectional-unadmitted-return-nontermination-20261116.md).
[Complete per-block fact trace](../../../../docs/reports/bidirectional-unadmitted-return-trace-20261116.md).

The exact T query has an extra NORMAL V return which paired C5 discards.
The complete NORMAL service cannot be certified, so the coarse T->U MAY
reply survives. A different exact U query does complete. The selected
completion/suppression mechanisms stay enabled.

- `UnadmittedReturn`: previous owner/controller plus the two new literal unary
  marking rules, including the V bootstrap query. C2/C5, caps, normal storage,
  packet filtering and accumulating Targets are reused.
- `ReturnPhase`: all regular run-index equalities, including completion guards.
- `ReturnFrozen`, `ReturnCold`: complete cold witnesses through run-10 and all
  within-run fixed points.
- `ReturnRounds`: executable witnesses for all delivery/publication stages at an
  arbitrary later field limit. Equal stages reuse their constructive proof.
- `ReturnKernel`: NORMAL V output, mark-selection liveness, disjoint V check,
  exact/coarse admission, missing-service rejection, actual completed U key and
  native root-MAY delivery facts.
- `ReturnSteady`, `ReturnRecurrence`: arbitrary-budget transitions and the uncapped
  run-9/run-10 recurrence; no earlier forward stop; persistent demand/Target;
  original input caps and Empty E throughout.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/unadmitted-return-cycle-20261116/check.py \
  --out /tmp/unadmitted-return-proofs
```

Optional `--dependencies` reuses an output of
`complete-point-service-20261116/check.py` after verifying every source hash.
The checker rebuilds these eight modules, compares unchanged policy bodies,
and audits every theorem. Only `propext` and `Quot.sound` are allowed.
There are no custom axioms, holes, classical choice or native_decide.
Keep compiled artifacts and receipts outside the repository.

A finite run-31 capture is diagnostic only. The proof establishes the
complete pair for every n>=0, with increasing field limits. This package
claims the stated scalar-core scope, not whole-engine/JVM/alias equivalence.
The native fixture's zero NORMAL report count differs from the reference's
run-3 NORMAL observation, as in the inherited example.

Validation: **171 new claims; 5,475 cumulative audited claims in 275 modules**.
Nine selected native component/control tests pass. All sources are hash-checked
before dependency reuse.

# Same-mark disjoint-return counterexample

Constructive Lean 4.35.0. Production is unchanged.
[Report](../../../../docs/reports/bidirectional-unadmitted-field-nontermination-20261116.md).
[Complete cold trace](../../../../docs/reports/bidirectional-unadmitted-field-trace-20261116.md).

The selected latest policy is unchanged. The synthetic leaf has two
same-mark NORMAL return regions, h.h and k. Callers read h; paired C5 drops
k, blocking whole and full-mark completion. Ordinary h reads renew root MAY.
The code has no loop, recursion, cleaner, pass rule or unresolved transfer.

- `FieldCycle`: fully analyzed unary marking actions plus ordinary caller h
  reads; unchanged C2/C5, completion/receipt checks and Target protocol.
- `FieldPhase`: generic run/parity equivalence after special early runs.
- `FieldFrozen`, `FieldCold`: explicit cold states through run-10, checked
  transitions and within-run quiescence at every step.
- `FieldRounds`: every delivery/publication stage at arbitrary budget 8+n;
  exact factorization and finite within-run fixed points.
- `FieldSteady`: arbitrary-budget saturation. The complete forward state
  stabilizes at run-11; the even state equals run-10 (also run-12).
- `FieldKernel`: same-mark disjoint C5 rejection, failed whole/U service,
  homogeneous-output conservativity, unchanged coarse/fine admission,
  ordinary field read and actual-packet coverage controls.
- `FieldRecurrence`: for every n, history(11+2n) and history(12+2n) equal the
  two complete states; persistent demand witnesses, non-stop test, Empty E
  and input caps. Demand frontier sizes are 70/82 and persistence size is 10.
- `FieldBounds`: plain H/Empty mx, output bounds, fixed-point controls.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/unadmitted-field-cycle-20261116/check.py \
  --out /tmp/unadmitted-field-proofs
```

Optional `--dependencies` reuses a completed
`mark-scoped-point-service-20261116/check.py` output after verifying every
source hash. The checker compares unchanged policy function bodies, builds
these nine modules and audits all 177 new claims. There are **5,766 cumulative
claims in 293 modules**. Only `propext` and `Quot.sound` are allowed; no
custom axioms, holes, classical choice or native evaluator are used.

Fifteen native component/control tests pass, including three new tests.
The finite unchanged full-program diagnostic reaches **run-31/POLICY**, with
zero NORMAL reports. The proposal reference retains a NORMAL observation
from run-5. No integrated production NE/completion implementation or
whole-engine/JVM/alias equivalence is claimed. The uncapped result is
proved for the executable proposal model, independently of the native cap.
Raw captures, compiled artifacts and receipts remain outside the repository.
No fix for this new counterexample is selected.

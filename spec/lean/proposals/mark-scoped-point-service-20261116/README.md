# Complete NORMAL terminal service per full mark

Constructive Lean 4.35.0. Production is unchanged.
[Contract and results](../../../../docs/reports/bidirectional-mark-scoped-point-service-20261116.md).
[Consolidated approach](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

- `ScopedCore`: full NORMAL closure with a projected terminal predicate; native
  observation preservation; positive sparse output classes; homogeneous-body
  conservativity; one-pass present/failure-set equivalence with per-mark scanning;
  internal-other-mark dependency rejection controls.
- `ScopedBody`, `LateScopedBody`: unchanged six-rule program, C2, C5, transfer,
  whole certificates and packet semantics, plus matching-mark completion/receipts.
  The latter makes new mark receipts usable only after handoff.
- `ScopedCold`, `LateScopedCold`: full cold states and within-run fixed points;
  natural run-5 / delayed run-7 stop, NORMAL observation from run-3, and uncapped
  quiet suffixes with accumulating Targets.
- `ScopedHomogeneous`, `ScopedRegression`: old homogeneous marked bodies create
  no additional flags for any query and store; no added filter can fire. Earlier
  FLOW, strict-MUST, protection and cleaner gates remain. The inherited old cold
  results remain valid through run-15.
- `ScopedProof`: selected-mark leaf closure/witness; missing same-mark, incomplete
  uniform, wrong-initial and DEMAND support rejection; native receipt and exact
  output-mark checks; NORMAL, protected and FLOW behavior preserved.
- `ScopedBounds`: new flags reference existing queries/NORMAL groups; only two
  additional flags in the new case; no V archive, extra NORMAL row or cap bypass;
  unchanged output bounds and Target accumulation.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/mark-scoped-point-service-20261116/check.py \
  --out /tmp/mark-scoped-point-proofs
```

Optional `--dependencies` reuses an output of
`unadmitted-return-cycle-20261116/check.py` after verifying every source hash.
The checker rebuilds these nine modules, compares unchanged program/policy
bodies, and audits every new theorem. Only `propext` and `Quot.sound` are allowed.
No custom axioms, holes, classical choice or native_decide are used.
Compiled artifacts and receipts remain outside the repository.

Validation: **114 new claims; 5,589 cumulative audited claims in 284 modules**.
**35 native component/control tests pass**, including six new adapter tests.
The unchanged native diagnostic remains run-31/POLICY with zero NORMAL reports;
the scalar reference retains its NORMAL observation from run-3. No integrated
production NE/completion implementation, universal termination, JVM/alias
refinement or project-performance claim is made.

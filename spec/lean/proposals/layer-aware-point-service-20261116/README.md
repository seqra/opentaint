# Separate NORMAL closure from plain return service

Constructive Lean 4.35.0. Production is unchanged.
[Selected contract and examples](../../../../docs/design/bidirectional-layer-aware-point-service-20261116.md).
[Complete updated trace](../../../../docs/reports/bidirectional-layer-aware-point-service-trace-20261116.md).

- `LayerCore`: NORMAL-layer and plain-service predicates; relevant H veto;
  old certificate implication and equality on unprotected return sets;
  generic relevant-observation preservation with full internal closure.
- `LayerBody`: exact unchanged protected-return program, C2/C5 and transfer;
  replace only the closure's layer predicate and reply-service predicate.
- `LayerCold`: complete cold states, within-run fixed points, natural run-5
  stop, NORMAL observation and uncapped quiet suffix from run-6.
- `LayerOldField`, `LayerOldExact`, `LayerOldMark`, and their `Cold` modules:
  rerun the three preceding program variants with the same new coordinator.
- `LayerProof`: full closure with protected states, actual plain NORMAL support,
  protected relevant/provider rejection, distinct H memberships, missing/DEMAND
  support and receipt controls, protected/NORMAL delivery retained.
- `LayerRegression`: unchanged old semantic cold states through run-6;
  generic guard bridge for the 18 older ordinary references and hole/alternating
  controls; old strict actual/candidate gates remain. Largest retained stop run-15.
- `LayerBounds`: current keys from existing queries, uncut NORMAL boundary states,
  reply subset, unchanged entry/output caps, no k summary archive or false
  whole/mark flags, monotone emitted Target state.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/layer-aware-point-service-20261116/check.py \
  --out /tmp/layer-aware-proofs
```

Optional `--dependencies` reuses a completed
`protected-return-cycle-20261116/check.py` output after verifying every source
hash. The checker source-compares every unchanged program, C2/C5, transfer,
whole/mark, receipt, publication, persistence and Target function. Only the two
selected predicate changes are allowed. It builds twelve modules and audits
**177 new claims; 6,279 cumulative claims in 324 modules**. Only `propext` and
`Quot.sound` are allowed; no custom axiom, hole, classical choice or native
evaluator is used. Compiled artifacts remain outside the repository.

All 57 selected native tests pass, including eight new controls. The unchanged
full-program diagnostic is **run-31/POLICY** with zero NORMAL reports; the
proposal reference retains its NORMAL observation at run-5. No complete
production NE/completion integration or whole-engine/JVM/alias equivalence
is claimed. Field limits and literal H semantics are unchanged. No new query,
summary, field path, cache class or cap exception is added. The repair preserves
the supplied examples; it is not a universal termination or performance theorem.

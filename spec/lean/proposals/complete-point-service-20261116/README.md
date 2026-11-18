# Complete NORMAL exact-point service

Constructive Lean 4.35.0 proof package. Production is unchanged.
[Contract and results](../../../../docs/reports/bidirectional-complete-point-service-20261116.md).
[Full current approach](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

- `CompleteClosure`: executable finite NORMAL closure; reachability and whole-return
  service witness; arbitrary continuation-observation preservation; composition;
  incomplete/C5-discarded-return rejection controls.
- `CompletePoint`, `CompleteService`: the previous exact-input program with unchanged
  C2, native operations and C5. Completion requires every unbounded leaf return to
  have an admitted NORMAL row. Delivery additionally requires all service to pass
  ordinary native application. No new input or field is generated.
- `CompleteCold`: complete cold states, all within-run fixed points, natural run-5
  stop and uncapped quiet suffix. NORMAL observation is retained from run-3.
- `LateCompletePoint`, `LateCompleteCold`: completion available only after handoff;
  the earlier Target stays emitted. Natural run-7 stop and uncapped quiet suffix.
- `CompleteBounds`: no extra query/cap exception, existing service rows and paired
  output bound. Only three existing exact keys carry completion.
- `CompleteRegression`: all old field-flow prepared keys are abstract and cannot
  certify this concrete-point service, including unreturned/compacted queries.
  Maximal-readiness checks cover the earlier conditional cold event subsets.
  Earlier observations/stops and MUST/protection fallback remain valid through run-15.

Run from the repository root:

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/complete-point-service-20261116/check.py \
  --out /tmp/complete-point-proofs
```

For a faster rebuild, pass `--dependencies` pointing to a prior
`exact-input-guard-cycle-20261116/check.py` output. The checker verifies every
inherited source hash before reuse, pins Lean, rebuilds these eight modules,
audits every new theorem, and permits only `propext` and `Quot.sound`.
No custom axioms, holes, classical choice, native_decide or oracle is used.
Compiled artifacts and receipts belong outside the repository.

This package checks **144 new declarations**, with **5,304 cumulative audited
declarations in 267 modules**. It does not prove whole-engine equivalence,
project performance or termination of every program. The complete-transfer
adapter is part of the certificate contract. The native tests exercise a
proposal adapter and unchanged production components, not an integrated
production implementation of NE/completion.

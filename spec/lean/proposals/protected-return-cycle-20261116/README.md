# Protected unrelated NORMAL return: uncapped cycle

Constructive Lean 4.35.0. Production is unchanged.
[Counterexample and exact scope](../../../../docs/reports/bidirectional-protected-return-nontermination-20261116.md).
[Complete per-block trace](../../../../docs/reports/bidirectional-protected-return-trace-20261116.md).

Three acyclic calls and six positive unary rules. The extra k rule assigns
its triggering mark to a fresh position. Native rule assignment therefore
makes its result protected while its layer stays NORMAL. Both selected
full-raw plain-support scans reject this unrelated return before h-region
projection. No loop, recursion, cleaner, configured pass or opaque transfer.

- `ProtectedReturn`: changed analyzed k actions and correct reverse transfers;
  all C2/C5, caps, protection, whole/mark/reply completion, receipt, publication,
  persistence, queues and ZERO/Target definitions remain source-identical to
  the latest `ReplyBody` policy.
- `ProtectedPhase`: generic later run/parity equality, including every selected
  completion and metadata function.
- `ProtectedFrozen`, `ProtectedCold`: explicit cold states through run-12,
  every transition, per-run within-run fixed points and reached-state proofs.
- `ProtectedRounds`: all delivery/publication stages at arbitrary budget 8+n,
  exact factorization and finite within-run fixed points.
- `ProtectedSteady`, `ProtectedRecurrence`: arbitrary-budget saturation and
  complete uncapped run-11/run-12 induction; persistent 70/82-row frontiers,
  non-stop checks, root Target/entry permissions and unchanged entry caps.
- `ProtectedKernel`: same-mark H witness for every supported point and limit;
  H is not a layer demotion; relevant h service and native receipt already
  succeed while the full-raw scan fails; k is uncut and not in steady NORMAL
  storage; all selected completion guards remain enabled and fail naturally.
- `ProtectedBounds`: current steady published data stays plain; output bounds
  and within-run quiescence remain unchanged. The raw k protection is intentional
  and is not incorrectly erased from the cold-prefix claim.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/protected-return-cycle-20261116/check.py \
  --out /tmp/protected-return-proofs
```

Optional `--dependencies` reuses a completed
`reply-scoped-point-service-20261116/check.py` output after verifying every
source hash. The checker builds these nine modules and independently audits
all **184 new claims; 6,102 cumulative claims in 312 modules**. Only `propext`
and `Quot.sound` are allowed; no custom axiom, hole, classical choice or native
evaluator is used. Compiled artifacts and receipts remain outside the repository.

All 20 selected native tests pass, including three new controls. The finite
unchanged diagnostic reaches **run-31/POLICY** and zero NORMAL reports;
the proposal reference retains a NORMAL observation from run-5. No complete
production NE/completion integration or whole-engine/JVM/alias equivalence
is claimed. The uncapped result does not use this finite native cutoff.

This is a counterexample to the **selected conservative executable adapter**,
not a refutation of the conditional geometric observation-preservation theorem.
H/NORMAL remain distinct. No repair is selected and production is unchanged.

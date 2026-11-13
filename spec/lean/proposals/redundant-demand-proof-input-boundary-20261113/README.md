# Limits of finite demand histories

13 November 2026. Proof component for `demand-task.md`. No analyzer or
classification change.

Let `obs(W)` be the complete allowed handoff history of program W. Let
`safe(W)` mean that deleting the selected row preserves its required
findings with no iteration limit. A history-only predicate must satisfy:

```text
remove(h) = true
    implies forall W, obs(W) = h implies safe(W)
```

[ObservationFiber.lean](ObservationFiber.lean) proves this obligation and
its converse. If two programs have the same history and one loses a valid
sink after deletion, a sound predicate must reject their shared history.
It cannot also select every program in which deletion is safe.

The [existing counterpair](../../../../docs/reports/bidirectional-same-prefix-latent-rename-20261112.md)
supplies the native example. Its 203 ordered observations agree through
H5. The kept controls finish at run-13. The single-row cuts finish at
run-11. Only program B loses U. These are natural ends, not iteration
limits. The Lean model proves the decision law; the native controls bind
the observed history and sink outcomes separately.

This is not a proof that the finite project corpus cannot be classified.
It is not a necessity certificate for actual OWASP target `1025a197…`.
No complete instruction model or CFG guard is authorized by this proof.
An edge-only operator theorem can still supply the required certificate,
as the accepted row-service law does.

Compile the dependency and model in a temporary directory:

```sh
scratch=$(mktemp -d)
cp spec/lean/proposals/redundant-demand-same-prefix-20261112/FiniteHistory.lean "$scratch/"
cp spec/lean/proposals/redundant-demand-proof-input-boundary-20261113/ObservationFiber.lean "$scratch/"
(cd "$scratch" && LEAN_PATH=. lean -o FiniteHistory.olean FiniteHistory.lean && LEAN_PATH=. lean ObservationFiber.lean)
```

All eight new axiom audits are empty. The sealed external native and
accepted-certificate rechecks are in
`redundant-demand-rows-20261112/cases/proof-input-obstruction-audit-v1/`.

[NormalClosure.lean](NormalClosure.lean) checks a second, narrower limit.
On a true EXACT input point, a NORMAL STAR/FLOW relation replaces a
prefix and preserves the remaining suffix. It cannot add a field absent
from both the input and the literal provider outputs. The model proves
this for the union of all finite compositions, with no bound on their
length. It computes a fresh field witness. Its nine claims use only
`propext` and `Quot.sound`.

```sh
lean spec/lean/proposals/redundant-demand-proof-input-boundary-20261113/NormalClosure.lean
```

The corresponding external package is
`cases/normal-envelope-composition-no-go-v1/`. It binds the actual OWASP
basis: 21 NORMAL STAR views, nine DEMAND MUST views and one ZERO identity.
The theorem excludes coverage by that fixed NORMAL library. It does not
exclude eventual recovery by DEMAND refinement, new body analysis or new
caller inputs. It supplies no actual-row verdict.

The accepted result stays 4,635 REDUNDANT, zero NECESSARY, 20,754 OPEN;
the separate joint cut stays 3,490.

Latest project reached/completed/accepted-forward runs remain OWASP
run-11/run-11/run-11, Conductor run-8/run-7/run-7 and Stirling-PDF
run-11/run-10/run-9. This proof runs no project analysis.

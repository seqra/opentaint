# Comparative no-loss proofs

The [audit and fix proposals](../../../demand-refinement-no-loss-audit.md)
state the baseline contract, the counterexamples and the status of every
rule. The [selected spec](../../../demand-refinement-and-termination.md)
contains the corresponding activation guards.

| Module | Claims | Result |
| --- | ---: | --- |
| [CoveredOrigin](CoveredOrigin.lean) | 7 | Legacy MAY and proposed NE make the same covered MAY reply in run-3. The native-shaped cold sequence reaches the second marking point precisely in run-5. Value-only omission stops at run-3, and no later suffix recovers the track. |
| [ServiceSimulation](ServiceSimulation.lean) | 14 | Constructive proof recipes require available inputs from legal runs and preserve every full derivation in the joint retained basis. A sealed stop contains every simulated track. A covered data token does not prove a source permission. The native guidance selector retains NORMAL ND and backward ZERO. The checked bundle or whole-scope native fallback keeps the baseline derivation. |
| [NativeAdmissionCells](NativeAdmissionCells.lean) | 5 | Same-head C2 cases compare the deployed scalar policy with the proposed family. Run-2 STAR replaces a baseline EXACT, later same-head STAR cases can lose a baseline command, and the MAY split keeps the old STAR and companion. |

This checker verifies the parent receipt and its 449 source hashes. It
compiles in Lean 4.35.0 and audits every new theorem's transitive axioms.
Only `propext` and `Quot.sound` are allowed.

```sh
python3 spec/lean/proposals/demand-no-loss-audit-20261117/check.py \
  --dependencies /absolute/external-data/demand-refinement-spec-20261117/checked-proofs \
  --out /absolute/external-data/demand-no-loss-audit-20261117/checked-proofs
```

The new receipt contains **26 claims**, with **7,527 cumulative claims in
452 pinned modules**.

`UniformCoverageOriginAuditTest` uses the native engine to compare the
baseline, the old value-only condition, and the condition that checks the
two sources. `LoopBlockExitBoundaryFindingTest` removes one selected
backward ZERO row from the after-loop scope. These are explicit adapters.
The [audit](../../../demand-refinement-no-loss-audit.md) states the
remaining native correspondence obligations. The generic guarded proof
does not establish complete extraction on arbitrary engine inputs.

## Termination guard checks

[GuardedTermination](GuardedTermination.lean) checks all eight NORMAL
generator routes in the alternating fixture, the two-source reply guard,
and the control-service condition for isolated terminal retirement.
It also runs controls with optional uniform value folding disabled.
The [catalogue checks](../termination-catalogue-verification-20261117/README.md)
exercise the guarded path with every bound reply retained.

After compiling the audit above, use its output and both dependency
directories on `LEAN_PATH`.

```sh
export ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0
export LEAN_PATH="$audit_output:$condensed_output:$two_sided_output"
lean -o "$audit_output/GuardedTermination.olean" \
  spec/lean/proposals/demand-no-loss-audit-20261117/GuardedTermination.lean
```

The additional module contains 11 audited claims. The combined receipt
contains 7,538 claims in 453 modules.

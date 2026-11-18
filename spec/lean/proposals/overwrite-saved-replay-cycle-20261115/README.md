# Ordinary-write saved-replay non-termination

Synthetic ordinary code and one FULL mark. This tests the selected
prepared-child saved-NORMAL replay approach with all earlier non-empty-MAY,
bounded-refinement and same-lane-uniform fixes. No loop, recursion, cleaner,
special pass rule, unresolved MAY transfer or predefined DATA summary.
Production is unchanged.

- `OverwriteReplay.java`: compilable ordinary code and the two call-site rules.
- `OverwriteConcrete.lean`: constructive all-word proof that the ordinary
  argument-to-return transfers are exactly the two derived records.
- `OverwriteReplay.lean`: prior executable owner/call machine extended with
  real strong-overwrite exclusions, native record reversal and E-aware matching.
- `OverwriteWitnesses.lean`: concrete complete states, not theorem assumptions.
- `OverwriteCold1..13.lean`: kernel-checked cold states, per-run quiescence,
  and handoff records.
- `OverwriteStable.lean`: complete C2/C5 packet at every later limit, and
  constructive induction of the same four nonempty rows for arbitrarily many
  handoffs. Exact/child probes and all paired exit selectors are included.
- `OverwriteControl.lean`: original caller offers, source permission,
  ZERO/Target admission and continued iteration. A NORMAL observation does
  not erase the anonymous demand Target.

The model covers the complete argument-to-return cone of this example.
Argument-side mutation and allocation cannot add a different input-derived
return provider. Four tests in `OverwriteSavedReplayCycleComponentsTest`
validate the decisive native operators. This is not an end-to-end native
implementation of the proposed changes or a general whole-core simulation.

The [report](../../../../docs/reports/bidirectional-overwrite-saved-replay-nontermination-20261115.md)
contains the code and every per-run demand, submission, initial and publication
through run-13. The exploratory reference also reaches run-61. Its finite
horizon is not a premise of the non-termination theorem.

Run with a **fresh external output directory**:

```bash
python spec/lean/proposals/overwrite-saved-replay-cycle-20261115/check.py \
  --out /absolute/external/fresh-proof-directory
```

The checker rebuilds the previous selected approach, then this package.
Python-generated witnesses are untrusted until Lean checks them. Every new
claim prints its axiom dependencies; only `propext` and `Quot.sound` are
permitted. No custom axiom, classical choice, admitted claim or native proof
shortcut is permitted. Logs, compiled artifacts and bulk JSON stay outside
this repository.

Latest validation: **88 new theorems, 998 audited declarations, 64 modules**.
All dependencies were rebuilt in a fresh external directory; the additional
three concrete-path theorems were then checked against unchanged dependency
hashes. All three depend on no axioms. The receipt is external
`docs/reports/data/overwrite-saved-replay-cycle-20261115/proofs-v1/receipt.json`.

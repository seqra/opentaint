# Descendant selected cleaner: uncapped cycle and R35

17 November 2026. Constructive Lean 4.35.0 model; FULL synthetic reachability.
Production code is unchanged.

[Complete code, per-run traces and semantic effects](../../../../docs/reports/bidirectional-cleaner-termination-campaign-20261117.md).

- `DescendantCleanerCycle.lean`: 20 claims. It models the old selected
  EXACT cleaner, including the same-head MUST exception, the cold source,
  observation, source permission, Target handoff, paired control C5 and
  computed empty-method identity. It proves a nonempty literal demand
  after every uncapped forward/backward pair. No field cut occurs.
- `ExactMUSTClosure.lean`: 13 claims. It closes the accepted selected
  EXACT/MUST policy under projection. An arbitrary path/E membership proof
  equates the conceptual partition with one input-shaped output. It keeps
  layers and unsupported branches, and proves NORMAL Target and empty
  demand at natural **run-1**. Exact nonuniform points still die.

R35 is a **semantic coarsening**, not exact point deletion. A selected
descendant point may remain NORMAL under a MUST input, as the same-head
point already could. No new field-cap exception is selected.

The companion [R36 package](../uniform-cleaner-spine-20261117/README.md)
checks these modules and their complete dependency closure, rejects proof
gap markers/custom axioms/classical choice, and runs the fresh cleaner
search. The native counterexample reaches **run-15/POLICY**; a finite
diagnostic is not the uncapped proof. General whole-analyzer soundness and
termination are outside these models.

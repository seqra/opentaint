# Demand-relative restriction: implementation adapter models

Date: 1 November 2026. Constructive specification and adapter evidence.

- [Specification](../../../demand-relative-summary-restriction.md)
- [Implementation proposal](../../../../docs/design/bidirectional-demand-relative-summary-restriction-implementation-20261101.md)
- [Implementation proof dossier](../../../demand-relative-summary-restriction-implementation-proofs.md)
- [Specification package](../demand-relative-summary-restriction-20261101/README.md)

```sh
python3 spec/lean/proposals/demand-relative-summary-restriction-implementation-20261101/check.py
```

The default checks the design's runtime baseline. After implementation,
use `--runtime-commit <reviewed-commit>` to bind the same mathematical
checks to the reviewed implementation bytes. The checker rejects a
worktree runtime difference from that explicit commit. The receipt states
which source revision it binds. This option does not prove the Kotlin
implementation; runtime tests and project measurements remain required.

The checker builds eight dependency modules and two local adapter modules
with Lean `leanprover/lean4:v4.33.1`. It uses a fresh ignored verification
directory, one worker/CPU, and a 768 MiB per-command Lean memory limit.
It audits all explicit public definitions, abbreviations, and theorems.
Only `propext` and `Quot.sound` are permitted axiom dependencies. Warnings,
classical choice, unproved declarations, unsafe/noncomputable/partial
definitions, and changed pinned specification/proposal bytes fail the check.

AdapterPipeline proves fixed-gate leaf/delta laws, complete-row provenance,
typed Reach saturation, and final admitted views. WorkloadAccounting proves
measurement distinctions and executable counterexamples to assigning
the cause from summary counts alone.

The [receipt](checks.json) binds models, proposal, specification, dossiers,
checker, and reviewed runtime source bytes. Hashes are correspondence
evidence, not Kotlin verification. Read the dossier for the exact scope.
The current inventory is 182 theorems (20 local adapter theorems) and
303 audited declarations across the ten modules.
This package does not prove general convergence, full finding equivalence,
or project performance improvement.

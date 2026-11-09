# Post-main migration proof package

This package checks the constructive component model for
[main-migration.md](../../../main-migration.md). Read the
[proof map](../../../main-migration-proofs.md) for the exact domain and limits.

The selected branch baseline is `14b8ac8354bfc824080e790c7d71f6cfae0f401a`.
The selected main is `54ad708fe1c4f551956d3d572866de1534415fa1`.
This task does not rebase or modify the analyzer.

From the repository root:

```bash
python3 spec/lean/proposals/main-migration-20261109/check.py \
  --output-directory /tmp/main-migration-proof-review
```

The output directory must be fresh. The pinned parent Lean toolchain selects
Lean 4.33.1. No extra Lean library is required beyond its Std/Lean libraries.
The checker compiles MainMigration to an external output directory, imports
it for an axiom audit, and checks every explicitly declared theorem. It does
not use an old compiled proposal in place of the current source.

- [MainMigration.lean](MainMigration.lean): executable definitions and 51
  kernel-checked theorems, including 11 finite example proofs.
- [AxiomAudit.lean](AxiomAudit.lean): reject custom axioms/classical choice or
  incomplete theorem output; allow only standard `propext` and `Quot.sound`.
- [manifest.json](manifest.json): exact source SHA-256 pins and revisions.
- [receipt.json](receipt.json): successful local check and honest proof scope.
- [axiom-audit.txt](axiom-audit.txt): each theorem's dependency list.

Source review rejects proof holes, native_decide and unselected unsafe or
noncomputable definitions. The model uses executable finite decisions and
structural proofs. Standard extensional equality dependencies do not give it
a choice oracle or a custom soundness axiom.

No native analyzer or whole-program convergence theorem is claimed. The
specification lists the Kotlin, model-loading and project validation gates.
Latest reached project iteration: not applicable.

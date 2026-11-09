# Main migration implementation proof supplement

Use the [implementation proposal](../../../../docs/design/bidirectional-main-migration-implementation-20261109.md)
and [specification proof map](../../../main-migration-proofs.md).

The supplement imports the pinned specification model. It adds executable
models of prepared pass-rule selection, atomic validation, canonical
per-action cleaner assumptions and effective legacy-cap isolation. It does
not change the specification or model a new AP operation.

From the repository root, with a fresh output directory:

```bash
python3 spec/lean/proposals/main-migration-implementation-20261109/check.py \
  --output-directory /tmp/main-migration-implementation-proof-review
```

The parent Lean toolchain selects 4.33.1. The checker compiles the original
MainMigration source, Plan, and the axiom audit into an external directory.
It checks all 51 specification laws and 19 implementation-seam laws, with
14 named finite example proofs. It rejects changed pins, proof holes,
custom axioms and classical choice. Only standard `propext` and `Quot.sound`
can occur in theorem dependencies.

- [Plan.lean](Plan.lean): implementation-seam definitions and 19 theorems.
- [AxiomAudit.lean](AxiomAudit.lean): check every declared law in both models.
- [manifest.json](manifest.json): pin proof sources, the spec, proposal and
  complete file/classification inventory.
- [receipt.json](receipt.json): actual component verification result.
- [axiom-audit.txt](axiom-audit.txt): all theorem dependency lists.

The cleaner-assumption theorem is conditional: it requires the assumed leaf
to hold in the supplied finite facts. It does not prove all native cleaner
approximations. The source-vector law checks configured action geometry and
original IDs before storage; it does not override canonical output storage.
The option law clears the ignored cap before shared prescan construction;
the original specification separately proves the diagnostic/schedule policy.

Native analyzer proved: false. Whole-program convergence proved: false.
Latest reached project iteration: not applicable. Kotlin correspondence and
project validation remain acceptance checks in the implementation proposal.

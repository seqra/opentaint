# Demand-relative summary restriction: constructive models

Date: 1 November 2026. Design proofs only. The runtime is unchanged.

- [Specification](../../../demand-relative-summary-restriction.md)
- [Proof dossier](../../../demand-relative-summary-restriction-proofs.md)
- [Proof guide](../../../proof-guide.md)

From the repository root:

```sh
python3 spec/lean/proposals/demand-relative-summary-restriction-20261101/check.py
```

The checker uses Lean `leanprover/lean4:v4.33.1`. It builds eight modules
in a fresh ignored verification directory. Each command uses one worker,
one CPU, and a 768 MiB Lean memory limit. A warning fails the check. It
audits every explicit public theorem, definition, and abbreviation.
Only `propext` and `Quot.sound` are permitted axiom dependencies. No
classical choice, unproved declaration, noncomputable function, unsafe
declaration, or partial definition is permitted.

The current inventory is 162 theorems and 112 executable definitions or
abbreviations: 274 audited declarations. The generated [receipt](checks.json)
records the exact declaration count,
specification hash, source inputs, and kernel command results. Hashes
bind reviewed source bytes; they do not verify Kotlin implementation.

The models prove local cut/restriction/admission laws, typed control
boundaries, finite progress traces, and a finite output-compression
witness. They do not establish general termination, full current-core
finding equivalence, or a project speedup. Read the dossier before using
a theorem as evidence for a wider claim.

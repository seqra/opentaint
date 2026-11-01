# Exact call-stage result merging: local analysis models

Date: 1 November 2026. Status: local constructive models PASS; future candidate not selected.

Read [the dossier](../../../call-stage-result-merging-analysis-proofs.md).
This is design evidence for a possible future optimization. It is not an
implementation, selection, or project-performance result.

The four modules model complete finite keys, explicit REACH/FLOW/TAINT
kind and ZERO/FLOW/full-mark symbol tags, exact ordinary equality,
protection OR, fixed deterministic OR-preserving suffix observations,
and the 64 -> 1 alias-continuation control (65 -> 2 with pass-through).
All definitions are executable. The final checker passes **44 theorems**
and audits **76 public declarations**. The only axiom dependency is
`propext`; there is no classical choice or unproved declaration.
See the [receipt](checks.json) for source hashes and command logs.

During the active project campaign, prepare the source inventory only:

```sh
python3 spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py --prepare-only
```

This performs Python source/manifest checks and writes a **NOT_RUN**
receipt. It does not start Lean, including its version command.
After the selected campaign has stopped, verify the model:

```sh
python3 spec/lean/proposals/call-stage-result-merging-analysis-20261101/check.py
```

The checker pins Lean `leanprover/lean4:v4.33.1`, compiles four modules with
one worker and a 768 MiB limit, and audits every explicit public definition
and theorem. It rejects warnings, unproved/noncomputable/unsafe/partial
source, unexpected imports, classical choice and unexpected kernel axioms.
The receipt hashes the models, checker, README, dossier and reviewed
runtime context. A source hash is correspondence evidence, not a proof of
runtime behavior.

The PASS receipt establishes only the listed local kernel checks. The model does
not prove stateful analyzer-hook equivalence, global scheduling, general
convergence, whole-project findings, or performance improvement. It does not prove AP
shape validation or arbitrary packed multi-mark Kotlin refinement. Its cost
model does not include measured map allocation/lookup costs. Those costs
and the actual duplicate-key ratio require future measurements.

# Candidate-directed static pruning

Status: **DRAFT / UNSELECTED — conditional constructive finite model**.
No runtime change is selected or implemented. Read the [proposal](PROPOSAL.md)
and [proof guide](../../../proof-guide.md).

```sh
python3 spec/lean/proposals/candidate-directed-static-pruning-20261103/check.py
```

The model compares the existing full normalized-survivor enumeration with a
candidate-only exact membership interface. It proves identical ordered observed
and lost raw IDs and identical peak metadata **if** the supplied oracle answers
exactly the old survivor-set membership for every candidate ID. The executable
reference oracle witnesses this prerequisite in the finite model by using the
old enumerated list. It offers no efficiency benefit and is not a Kotlin adapter.

The model includes pair normalization, FLOW exclusion removal, abstract MUST to
ANY, both layers, ignored protection and raw-ID collisions after normalization.
A concrete witness keeps a colored candidate lost when the old emitted survivor
list contains only a FLOW row. Logical FLOW coverage cannot replace membership.
The empty-candidate plan requests neither common nor private-B enumeration and
never calls the row lookup or oracle. Cost laws count caller materializations,
including a nonempty-candidate strict witness; oracle-internal cost stays explicit.

The checker pins immutable 050b production reference blobs, compiles with
Lean 4.33.1 on one worker, and audits every explicit public definition/theorem.
The receipt and audit are portable. Kotlin oracle correctness, ownership,
iteration over real packed AP stores, cancellation/exception behavior, runtime
semantics, memory savings and project speedup remain unproved and unmeasured.

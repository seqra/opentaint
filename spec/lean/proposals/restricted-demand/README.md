# Restricted demand and static closure

Proposal only. The analyzer implementation is unchanged. The selected repair
is [static demand closure and run-1 exit routing](../../../restricted-demand-static-closure.md).

[Design and embedded control evidence](../../../../docs/design/bidirectional-restricted-fact-management-20261027.md)
states the baseline storages, pipeline and gap. `RestrictedDemand.lean`
uses the original AP `emitW` and `restrictI`. Ten local constructive theorems
pass. `checks.json` records the successful audit and seven actual Kotlin
AP/store control outcomes.

The model checks the demand gates for the stated run-1 export shapes. The
Kotlin controls check reverse-shaped body operations and the same gates.
Neither is a complete JVM compiler or whole-iteration proof. No completion
algorithm is proved by the two exact missing-pair witnesses.

`checks.json` preserves the historical pre-selection receipt. Its
`REPAIR_UNSELECTED` state is not the current policy. The separate
`static-closure-checks.json` records the selected completion model.

`StaticClosure.lean` proves equality between eager guidance closure and
factored seed paths, with executable witnesses in both directions. It also
checks mark composition and the generic exit-handler contract. Its 18
audited declarations pass; the core closure equivalence uses no axioms.
AP geometry, FULL/GROUP adapters and real JVM exit delivery remain explicit
implementation obligations in the specification.

`closure_oracle.py` compares the eager and factored concepts on 91 finite
graphs. It also checks three generic exit-handler cases. It does not execute
the analyzer. Run it with an optional output path:

```sh
python3 proposals/restricted-demand/closure_oracle.py /tmp/static-closure-results.json
lean -j 1 -M 512 proposals/restricted-demand/StaticClosure.lean
```

From `spec/lean`, after the existing AP dependencies have been built:

```sh
LEAN_PATH=.lake/build/lib/lean lean -j 1 -M 512 proposals/restricted-demand/RestrictedDemand.lean
```

Only `propext` and `Quot.sound` occur in the combined axiom audits. There is no
classical choice, new axiom or unproved placeholder.

# Complete loop-observation selection: local model

Proposal: [next iteration](../../../../docs/design/bidirectional-full-mark-and-loop-work-next-iteration-20261112.md).

`ObservationPlan.lean` checks seven constructive local claims for complete
C2 extra witnesses, first-choice selection, all-bad raw fallback and exact-key
query equality. The abstract observation contains separate canonical C2 and
enclosing result lists. Native descriptors must map injectively to those IDs.

This model does not prove native query-key completeness, batch application,
source/control boundary filtering or real replay equivalence. Those are open
activation gates. No current analyzer code uses this new model.

Run with Lean 4.35.0:

```sh
lean spec/lean/proposals/loop-observation-work-20261112/ObservationPlan.lean
```

The checked receipt and first failed external attempt remain under
`/drive-testcomp/opentaint-go-rules/work-reduction-20261112/analysis/conductor/`.
The model uses no `sorry` or classical choice. Each extra witness is returned
by an executable finite-list search. Printed axiom audits are local-model
evidence, not a whole-analyzer verification.

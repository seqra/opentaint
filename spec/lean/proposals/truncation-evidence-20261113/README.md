# Truncation evidence: empty suffix and symbolic STAR

This package supports the [investigation](../../../../docs/reports/bidirectional-truncation-evidence-20261113.md).
It does not change the analyzer.

```sh
lean spec/lean/proposals/truncation-evidence-20261113/Evidence.lean
```

Lean 4.35.0 checks the model. There are no `sorry`, custom axioms, or
classical choice. Printed dependencies are standard `propext` and
`Quot.sound` only. Existence proofs provide explicit paths.

| Theorem | Scope |
| --- | --- |
| `mayEmpty_exact` | The bit says exactly whether the recorded suffix language includes the empty path. Missing evidence means unknown. |
| `merge_denotes`, `merge_empty` | Union all contributors. Join the bit with OR. Unknown absorbs known evidence. |
| `lost_field_excludes_empty` | A removed known field makes every binding of the old tail nonempty. |
| `reject_exact_empty` | Reject an exact empty binding **if** the evidence covers every relevant binding. Capture completeness is an explicit hypothesis. |
| `rejecting_star_by_known_chain_is_not_binding_safe` | A STAR frame with no known extra fields still has a relevant nonempty binding. The proposed direct rejection is not a valid binding filter. |
| `deeper_star_can_match`, `unrelated_field_has_no_binding` | Full suffix evidence distinguishes a matching first field from an unrelated first field. The one-bit form cannot make this distinction. |

The model has finite exact/open suffix patterns, one base and mark, and
empty exclusions. It models bindings, not uniform taint. It does not model
all C2/C5 cells, aliases, ND, controls, persistence, or arbitrary future
analyzer executions. In particular, the conditional exact-empty theorem
does not authorize an analyzer-wide admission change.

The native counterexample checks the missing operational step: a caller
can construct a STAR offer from MAY without carrying the callee's cut
evidence. Rejecting that offer loses a real finding despite saved NORMAL
replay. Its two uncapped controls finish naturally at run-7 and run-5.
The report gives the complete relevant trace and evidence location.

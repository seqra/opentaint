# Restricted demand and static closure

Implementation is in progress. The 28 October user decision selects Empty
field E for abstract STAR demand. The exclusion-union candidate below is
superseded. See the [follow-up review](../../../../docs/design/bidirectional-restricted-demand-followup-20261028.md)
for the STAR validator and killed-write/pool-supply distinctions. The
27 October open cases are recorded in the
[implementation checks](../../../../docs/reports/bidirectional-restricted-demand-validation-20261027.md).
The [candidate repair design](../../../../docs/design/bidirectional-restricted-demand-open-contracts-20261027.md)
makes these choices concrete. It does not select their behavior. The
candidate proof files below are not runtime implementation authority.
The selected repair
is [restricted-run demand, static handoff closure and run-1 exit routing](../../../restricted-demand-static-closure.md).
That specification is self-contained: it states original, current and
proposed behavior, the complete pipeline, proofs and the removal ledger.

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
checks mark composition and the generic exit-handler contract. Its 23
audited declarations pass; the core closure equivalence uses no axioms.
Endpoint witnesses and the required-path guide are executable. The unique
normal-exit laws preserve the input and execute only the selected handler.
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

The historical second review adds `MarkBoundaryReview.lean` (18 audited
declarations) and `EmissionRestrictionProbe.kt`. The probe describes runtime
core `57ca8d4940e8fb52e7eed6151928d4025c7d7ad9`, before this implementation.
`boundary-review-checks.json` records the complete outputs. The probe
passes 14 original mark/STAR behavior checks and confirms two required
corrections: ancestor E rebasing for concrete STAR, and the current
MUST-input/STAR-demand adapter rejection. It does not apply those fixes.
Do not run its expected-defect assertions as tests of the repaired runtime.
The original handoff keeps STAR/E; the selected proposal now removes the
later STAR-to-ANY widening and updates the demand-adapter contract.

`RestrictedProtection.lean` checks the metadata transport used by paired
summary restriction. A protected input leaf uses the same partial restriction
as the ordinary leaf. Four constructive lemmas show that every surviving
protected result keeps its flag, every flag has an input witness, and flagged
results remain a subset of ordinary results. This is a local list model;
the typed adapter is also checked by `RestrictionTest` with mixed marks and
changed paths and tails. It does not prove the complete analyzer.

`StaticProducer.lean` is historical evidence for the removed pre-exit
producer replay mechanism. It checks that former binding route.
Its seven constructive audits use no axioms. The model relates each finite
old early-W actual-binding derivation to the producer route with the same
bindings. It also checks that producer delivery cannot emit an ordinary
summary, record or CFG result. It assumes the existing actual AP binding
contract; it does not prove the complete JVM interpreter or scheduler.

`ExcludedFlowCandidate.lean` has six historical constructive audits for the
unselected, now superseded excluded-STAR repair. It keeps a satisfied shared FLOW initial. For the
remaining same-path STAR case, it unions the field exclusions. It reuses
the original AP algebra. MUST projection, packed equivalence and complete
iteration behavior remain separate obligations. The full local audit is
in `excluded-flow-candidate-checks.json`.

`StaticInputGrammar.lean` has 15 constructive audits for the selected
named-field STAR input-domain repair. It proves the local grammar
extension and bounded STAR relay. Two laws reuse the correlated AP model
for actual identity and field-limit operations. Caller supply, accessor
tags and identity static projection are explicit assumptions. The full
local selected audit is in `static-input-grammar-checks.json`; the earlier
candidate receipt is historical. The first
512 MiB proof attempt ran out of memory; the successful audit used 2 GiB.
These proof-tool limits are not project-analysis configurations.

`PreExitGuidanceCandidate.lean` has nine historical constructive audits
for the superseded live pre-exit guidance candidate. It transports finite routes when all
required primitive keys are captured. Actual caller bindings are explicit
input to the model. It constructs local, two-wrapper and genuine ZERO
witnesses, and checks relational call factorization. The key-coverage and
origin-factorization premises still need their production adapter proofs.
The local model does not establish those premises, scheduling fairness,
or whole-iteration completeness. The complete audit output is in
`pre-exit-guidance-candidate-checks.json`.

`AbstractDemandEmptyExclusion.lean` checks the selected 28 October rule in
19 local constructive audits. Normalize abstract STAR demand copies on
both entry and exit. Concrete E, actual E and native records remain
unchanged. The model proves shared-start C2 against normalized demand,
retained raw C5 pairs and layer, and actual-E-aware matching. It includes
an explicit witness for widened abstract exit permission. It does not
prove the complete typed adapter, JVM or iteration pipeline.

`LocalStaticWriteSupply.lean` checks the selected write-point supply rule
in 14 local audits. It preserves the FLOW writer and the actual output
mark, checks exit independence and idempotent pool union, and introduces
no NORMAL record or runtime support flag. The receipt is
`local-static-write-supply-checks.json`.

`KilledStaticWrites.lean` has 25 local audits for conservative pending-key
capture and final pruning, including decreasing survivor membership.
Caller binding uses only primitive/recursively bound seeds and explicit
actual binding steps. Static closure transport follows the frozen seed
inventory. Actual JVM observers and binding export remain production
adapters, not conclusions of the local proof. The complete receipt is
`killed-static-writes-checks.json`.

`WriterBindingScope.lean` has six local audits showing why exact AP tail
keys need not commute under binding/composition reassociation. This fixes
the theorem scope: exact eager/factored equality is for static closure of
the same frozen bound inventory. The receipt is
`writer-binding-scope-checks.json`.

# FLOW demand mask audit

17 November 2026. Constructive Lean 4.35.0. Production unchanged.
[Consolidated contract](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../../proof-guide.md).

**27 new constructive claims; 7,187 cumulative claims in 413 checked modules.**
This package rejects a candidate missed-observation example by restoring an
existing boundary operation in its model. It selects no new analyzer behavior.

The synthetic helper reads p.f, clears T at the returned root, and returns
it. Its caller supplies U, where U != T. Run-1's FLOW return excludes T.
A model that copies this mask directly into next-run demand rejects a nested
unmasked FLOW probe and loses U. Those rows are **invalid under AP F72**:
both FLOW demand endpoints have Empty mx. The actual handoff admits the
probe, learns the masked NORMAL relation and retains U at **run-3**.

`MaskHandoff` separates the two scopes:

- First 16 claims: local algebra and the **invalid unprojected countermodel**.
  These do not prove a failure of the selected analyzer.
- Final 11 claims: actual guidance projection, unchanged path/tail/base/E and
  concrete mark, idempotence, correct own-row C2/C5, arbitrary finite wrapper
  depth, preserved NORMAL-record mask, U preservation and T rejection.

The projection changes guidance only. Runtime facts and saved NORMAL records
keep mx. The native test checks actual demand admission before running each
backward owner. It uses native transfers, C2, C5, persistence and driver;
there is no rejection or transfer adapter.

Five native tests make 16 cold executions: one nested baseline, direct and
no-cleaner controls, twelve combinations of wrapper depth 1..6 and
EXACT/MUST U inputs, and the exact cleaned-T negative. All finish naturally
at **run-3**. They have no real field cuts, loops, recursion, aliases or ND.
R31's disjoint branch and R32's STAR guard are inactive in the failure cell.
These controls do not establish whole-proposal integration or G1–G4.

```bash
python3 spec/lean/proposals/handoff-mask-audit-20261117/check.py \
  --out /tmp/handoff-mask-proofs
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.MaskedFlowRelaySoundnessTest --offline
```

The checker verifies dependency source hashes and transitive axioms. Only
`propext` and `Quot.sound` are allowed. Compiled data and logs stay outside Git.

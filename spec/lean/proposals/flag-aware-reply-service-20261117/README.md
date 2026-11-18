# Complete NORMAL return service within each literal H class

Constructive Lean 4.35.0. Production unchanged.
[Selected rules, example, costs and validation](../../../../docs/design/bidirectional-flag-aware-reply-service-20261117.md).
[Complete updated trace](../../../../docs/reports/bidirectional-flag-aware-reply-service-trace-20261117.md).

The new delivery check projects terminal obligations onto the reply's AP
region and exact H class. Full internal NORMAL closure is not projected.
Every selected return needs its whole same-H admitted NORMAL service and
an actual same-context native image. Protected/plain store copies remain
separate. NORMAL outputs and already emitted Targets are not removed.
Protected originals remain a conservative fallback.

- `FlagCore`: constructive same-flag whole-service/receipt witnesses,
  wrong-flag rejection, full-closure and generic continuation theorem.
- `FlagBody`: unchanged two-rule protected-return program and analyzer,
  with only the new delivery check and original H passed from the current packet.
- `FlagCold`: cold transitions and fixed points, natural run-5 stop with
  NORMAL observation, retained run-3 Target and uncapped quiet suffix.
- `FlagOldUnrelated/Field/Exact/Mark` and their `Cold` modules: the four
  previous program variants retain their complete checked cold histories.
- `FlagProof`: full internal closure, same-H native receipts, missing/wrong
  service, original H fallback, unchanged NORMAL delivery and old shape guards.
- `FlagRegression`: 21 older ordinary/hole/alternating current-reply inventories
  stay plain; their old guard bridge rejects the new path. Largest old stop run-15.
- `FlagBounds`: no new query keys, unchanged C2/C5 caps and reply subset,
  owner-local status, NORMAL basis and accumulated Targets.

```bash
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
python3 spec/lean/proposals/flag-aware-reply-service-20261117/check.py \
  --out /tmp/flag-aware-proofs

ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 LEAN_PATH=/tmp/flag-aware-proofs \
lean scripts/demand_experiments/flag-aware-reply-service-20261117/Explore.lean \
  > /tmp/flag-aware-cold.txt
python3 scripts/demand_experiments/flag-aware-reply-service-20261117/render.py \
  --data /tmp/flag-aware-cold.txt --out /tmp/flag-aware-trace.md

./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.ProtectedReplyServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.RelevantProtectedReturnCycleTest \
  --tests org.opentaint.dataflow.bidi.LayerAwarePointServiceNativeTest --offline
```

Optional `--dependencies` reuses completed
`relevant-protected-return-cycle-20261117/check.py` output after every source
hash is verified. All existing analyzer definitions are source-compared.
Only `actualReplies`, `round` and `deliverAt` change, to perform selection and
pass the existing packet H. A new predicate supplies the additional check;
C2/C5, rule transfer, closure, storage and Target functions are source-identical.

Audit: **136 new constructive claims; 6,591 cumulative claims in 347 modules**.
Only `propext` and `Quot.sound` are allowed; no classical choice, custom axiom,
hole or native decision oracle is used. All **19 selected native tests pass**.
The unchanged full-program diagnostic is run-31/POLICY with zero NORMAL
reports; the proposal reference retains its run-5 NORMAL observation.
There is no production integration or whole-engine equivalence claim.
No query, propagated path, archive, persistent region table or field-cap
exception is added. No universal termination theorem is claimed. Keep the
next counterexample search separate from this repair's established scope.

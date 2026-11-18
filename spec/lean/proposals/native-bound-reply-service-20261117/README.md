# Native-bound NORMAL reply service

17 November 2026. Constructive proposal model. Production is unchanged.
[Selected rule](../../../../docs/design/bidirectional-native-bound-reply-service-20261117.md).
[Complete annotated traces](../../../../docs/reports/bidirectional-native-bound-reply-service-trace-20261117.md).

`BoundCore` compares the full native bound images of an existing strong
NORMAL EXACT/MUST query with already committed NORMAL data. Same effective
H, base and full mark are mandatory. Whole MUST coverage respects real E.
Internal closure remains unprojected. Stored literal H memberships are not
merged. NORMAL output, saved replay and owner DEMAND handoff stay intact.

`BoundBody` uses the protected-input counterexample's exact code and the
previous analyzer definitions. Only `bodyClosed` and `actualReplies` change;
new helpers implement the selected delivery certificate and the native H
binding view. `check.py` checks this source boundary. The model binding view
repairs an earlier model omission: production already transports incoming H.
It does not authorize a new production field or layer transfer.

Validation: **246 new constructive claims; 7,009 cumulative audited claims
in 399 source-hash-checked modules; 19 native component tests pass**.

The proof covers:

- Native binding geometry, input H, local H and mark restoration.
- Constructive whole-region NORMAL witnesses with the bound H and full mark.
- Complete owned graph closure and arbitrary coverage-respecting continuation observations.
- Simultaneous witnesses from the same native packet.
- Exact preservation of current owner DEMAND handoff rows and existing persistence.
- No extra query, propagated path or cap exception; current delivery is a subset.
- The protected-input reference: NORMAL observation at run-5, natural empty
  forward frontier at run-7, and an uncapped quiet suffix.
- The uniform-input reference: NORMAL observation at run-7, natural empty
  forward frontier at run-9, and an uncapped quiet suffix.
- Five earlier complete service references: natural run-5 stops and all
  observations retained. Their coordinator metadata may differ.
- The explicitly enumerated 252-configuration family: a natural empty
  frontier by run-9, observations equal to its uncapped concrete reference,
  and no revival at any later run. This is a finite family theorem, not a
  theorem for every acyclic program.

Every cold transition has a checked within-run fixed point. The reference
controller accumulates Targets over the complete round history. It does not
cancel an earlier Target to obtain completion. No hard limit proves a demand
redundant. The family scan additionally runs through run-25; this finite
capture is diagnostic only.

Only the finite positive-unary leaf adapter has an executable full-closure
implementation here. The generic theorem requires a valid complete adapter
for any wider graph. ND, aliases, cleaners and other effects must not be
silently omitted to enable it. Their earlier proof scopes and fallback
policies remain. Native tests check existing AP components, not integration
of the complete proposal. The unchanged production diagnostic remains
run-31/POLICY with its documented observation alignment difference.

```bash
python3 spec/lean/proposals/native-bound-reply-service-20261117/check.py \
  --out /tmp/native-bound-reply-proofs
ELAN_TOOLCHAIN=leanprover/lean4:v4.35.0 \
LEAN_PATH=/tmp/native-bound-reply-proofs \
  lean scripts/demand_experiments/native-bound-reply-service-20261117/Search.lean
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.BoundNativeReplyServiceNativeTest \
  --tests org.opentaint.dataflow.bidi.ProtectedOriginalCycleTest \
  --tests org.opentaint.dataflow.bidi.ProtectedReplyServiceNativeTest --offline
```

`check.py --dependencies PATH` can reuse an audited parent receipt. It checks
every dependency source hash before copying compiled modules, compiles each
new source and audits each theorem's transitive axioms. No classical choice,
custom axiom, proof hole or external decision oracle is accepted. Only
`propext` and `Quot.sound` are permitted.

All compiled modules, receipts, search captures, XML and logs are external:
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/native-bound-reply-service-20261117/`.

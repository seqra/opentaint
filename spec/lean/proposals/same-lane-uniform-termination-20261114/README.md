# Same-lane uniform termination

[Approach](../../../../docs/design/bidirectional-same-lane-uniform-termination-20261114.md)
and [annotated trace](../../../../docs/reports/bidirectional-same-lane-uniform-termination-reference-20261114.md).
Production is unchanged.

- `UniformService.lean`: extend the old neutral coverage predicate to a
  diagonal full-mark lane and equal FLOW mx, retaining identical literal H.
  Prove constructive point coverage, mark gates, retained NORMAL providers,
  class separation and rejection of STAR/MAY/backward candidates.
- `MarkedClosure.lean`: execute every run-1 output, all run-2 paired rows,
  the complete run-3 C2/body/C5 packet, concrete and FLOW/mx lanes, returned
  EXACT/MUST facts and the extra EXACT-triggered FLOW probe. Prove the
  complete frontier is empty and all later delivery-closure rounds are the
  same, by induction on their count.
- `PacketOrder.lean`: reproduce a stale descendant's extra STAR query;
  check that complete reply folding avoids it. Prove semantic membership
  after folding is independent of enumeration order within the packet.
- `Acceptance.lean`: apply the extended predicate to every older method,
  BB, neutral, warm-record, wrapper and selected-cleaner acceptance case.

```sh
python3 spec/lean/proposals/same-lane-uniform-termination-20261114/check.py \
  --out /tmp/same-lane-uniform-termination-proof
```

The checker first rebuilds every earlier proof package. It audits every
new theorem and rejects warnings, holes and custom/classical axioms. Only
`propext` and `Quot.sound` are permitted. Logs, source hashes and the receipt
go to the requested output directory.

Latest check: **PASS, 401 declarations, 25 modules, 42 new claims**.
Receipt: `same-lane-uniform-termination-20261114/proofs-v3/receipt.json`
in the external report-data archive. The new closed reference finishes
**run-3**, as do the old method/BB and ordinary double-write references.
The standalone selected MUST cleaner finishes **run-1**. No hard iteration
limit occurs in the new closure proof or the old recurrence induction.

Native tests of provider/application components pass separately. They do
not install NE or establish whole-native termination. No project scans
were rerun. The proof scope is the supplied positive field-transfer call
graphs with explicit complete owner publication/reply batches; it is not
universal JVM, alias or arbitrary asynchronous-service correspondence.

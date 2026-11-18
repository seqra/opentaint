# Bounded MAY/MAY query-partition investigation

This is a candidate reference, not a selected production change. Read the
[investigation report](../../../../docs/reports/bidirectional-may-may-progress-investigation-20261114.md)
for explicit admission changes and the native proof gaps.

- `Partition.lean`: constructive, finite partition coverage for arbitrary
  point transfers, query count/depth bounds, no MAY/NE premises.
- `Investigation.lean`: cleaner countercheck; retained NORMAL guard
  derivation; neutral prefix provider coverage; guarded C2 plan and paired
  C5; actual two-call replay and natural run-5 stopping in the declared
  method-only / BB-method reference.

The candidate uses retained NORMAL input guards and finite AP queries.
It does not compose full field evidence through calls. The old references
are imported unchanged. The prototype partitions Empty-E conditional FLOW
queries only; it does not establish general concrete, alias or ND coverage.

Run into a fresh external artifact directory:

```bash
python3 spec/lean/proposals/bounded-may-partition-20261114/check.py \
  --out /tmp/bounded-may-partition-proof
```

The checker compiles dependencies, checks each `#print axioms` result and
records source hashes. Only `propext` and `Quot.sound` are allowed. There
are no admitted proofs, custom axioms or classical choice.

Checked result: **8 modules, 163 audited declarations** (38 new, 125 imported).
The frozen external receipt is
`/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/bounded-may-partition-20261114/proofs-v8/receipt.json`.
Both scoped reference frontiers are empty after run-5; general/native
termination remains unproved.
The package also checks a longer-read guard-bootstrap limitation and the
local progress of retaining the next bounded cut prefix. It does not prove
an engine-wide guard-history progress algorithm.

# EXACT point write progress

Follow [proof-guide.md](../../../proof-guide.md). Production is unchanged.
Read the [approach](../../../../docs/design/bidirectional-exact-point-write-progress-20261115.md)
and [validation report](../../../../docs/reports/bidirectional-exact-point-write-progress-20261115.md).

One semantic change: remove the EXACT/FLOW contribution to a strictly deeper
excluded identity keep. Same-head exclusions and all value writes remain.
C2, C5, raw-to-public normalization, cuts, marks, protection, calls and
ZERO/Target handling are unchanged. No child-cover or evidence store is added.

| Module | Obligation |
|---|---|
| `PointWriteReplay` | Existing full unary call/core-form pipeline, with only the point correction |
| `PointWriteProperties` | Generic exact-point incompatibility, native retained replies and NORMAL results, unchanged operand classes, point/descendant family geometry, fixed-plan work bound |
| `PointCertificate*` | 12 complete old references plus 6 new references: cold closure, quiescence, paired handoff, actual marked packets, producer permission, natural stop and expected observations |

Every old reference state, incoming/outgoing frontier and saved basis is equal
to the earlier exclusion-aware execution. Older cleaner/protection proofs are
unchanged dependencies. New nested-write references naturally stop at run-3,
run-5 or run-11. Latest required reference: **run-15** (the unchanged Double
case). Wider diagnostic cases reach at most **run-13**.

Final audit: **596 new theorems, 2,083 audited declarations, 105 modules**.
Only `propext` and `Quot.sound` are allowed. No custom assumptions, classical
choice, placeholders or external proof oracle. No hard iteration limit
justifies stopping; final DATA and Target frontiers are checked empty.

```bash
python3 spec/lean/proposals/point-write-progress-20261115/check.py \
  --out /tmp/point-write-proofs
```

The default rebuilds the previous proof package. `--dependencies DIR` can
reuse an audited build after checking every source hash. It still compiles
and audits every new module. The final receipt lists every source hash.

Freeze witnesses independently of Lean:

```bash
python3 scripts/demand_experiments/point-write-progress/capture.py \
  --out /tmp/point-write-data --lean-dir /tmp/point-write-cold
```

Scope: synthetic ordinary unary core-form return cones, original concrete
caller packets and call/Target controls. The nested-write form is supported
by the core; JVM lowering and whole-production equivalence are not proved.
Native tests use a candidate filter around existing operators, rather than
changing production. Bulk data and compiled output stay outside the repo.

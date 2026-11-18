# Disjoint selected-cleaner FLOW repair

17 November 2026. Constructive Lean 4.35.0. Production unchanged.
[Selected delta, trace and costs](../../../../docs/design/bidirectional-disjoint-cleaner-flow-20261117.md).
[Consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

A selected nonstatic FULL cleaner keeps a FLOW path unchanged only when
its entire suffix cone is outside the cleaned region. Ancestor EXACT probes
still use the old mask, because later STAR normalization can cover the
cleaned field. Concrete cleaner rows, requests, C2/C5, caps and Targets are
unchanged. The rule never removes an existing mx exclusion.

**27 new constructive claims; 7,108 cumulative across 409 hash-checked modules.**

- `DisjointCleaner`: arbitrary-path whole-cone disjointness; identity of
  the concrete cleaner for every full mark/suffix; exact-normalization
  guard; unchanged concrete/header coordinates; complete packed-path
  partition with no duplicate or new path.
- `CleanerRepairTrace`: unchanged run-1 and C2; complete own-row run-2 C5
  now constructs a NORMAL FLOW record; marked/protected rows remain;
  saved correlation transports arbitrary suffixes; the repaired example
  reaches a NORMAL observation and stops at **run-3**, with an uncapped
  report-preserving quiet suffix.

The parent is the soundness audit, including its historical failing model.
The new helper body is source-identical; its selected cleaner operation is
changed. Initial policy, transfers, C5 and binding are imported unchanged.
The checker validates source hashes and each theorem's transitive axioms.
Only `propext` and `Quot.sound` are permitted. No classical choice, custom
axiom, hole or external proof oracle is accepted.

**60 native tests pass**: the earlier 53 plus seven repair components. The
new adapter uses existing C2, C5, record persistence view, reversed native
application and marking checks. It also covers sibling paths, real E/mx,
DEMAND layers, real cuts, old requests, concrete cleaners and the exact-root
normalization hazard. The component pipeline gets its NORMAL provider at
run-2 and its NORMAL observation at run-3. It is not an installed proposal
or a patched cold driver. The original cold loss diagnostic still stops
at run-3 with zero observations; its two controls each retain one.

The earlier no-cleaner family uses unchanged operations: 252 cases, stops
by run-9, diagnostic scan through run-25. Older concrete cleaner controls
retain their proved concrete transfer. No whole-analyzer relevance,
termination or native integration theorem is claimed.

```bash
python3 spec/lean/proposals/disjoint-cleaner-flow-20261117/check.py \
  --out /tmp/disjoint-cleaner-proofs
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DisjointCleanerFlowNativeTest \
  --tests org.opentaint.dataflow.bidi.CleanerGetterAdmissionSoundnessTest --offline
```

`--dependencies PATH` can reuse the source-checked parent receipt. All
compiled objects, receipts, XML and logs are outside the repository:

```text
/drive-testcomp/opentaint-go-rules/report-data-archive/opentaint-w3/docs/reports/data/disjoint-cleaner-flow-20261117/
```

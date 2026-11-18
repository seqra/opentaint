# Run-2 STAR relay proof

17 November 2026. Constructive Lean 4.35.0. Production unchanged.
[Selected change and complete trace](../../../../docs/design/bidirectional-run2-star-relay-20261117.md).
[Consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

Run-1 writes leave exclusion-free DEMAND preservation relations. Run-2
needs to relay same-head STAR queries to learn the NORMAL exclusion-guarded
relation through wrappers. This package replaces only that rejection and
uses the same emitter in C5's complete raw image. It adds no cap exception.

**36 new constructive claims; 7,160 cumulative claims in 412 hash-checked modules.**

- `Run2Relay` (24): exact phase/shape guard; old C2 and paired C5 preservation;
  constructive offer witnesses; maximum two starts; unchanged requested
  head and both field bounds; actual/demand E controls; concrete DEMAND and
  conditional NORMAL FLOW companion; wrong mark/base, mx, exact demand and
  backward MUST rejection; same-head raw STAR permission at the field cap.
- `RelayTrace` (12): unchanged run-1 records and both pairs; outer deeper
  admission and inner same-head relay; computed NORMAL strong-write C5;
  arbitrary finite wrapper depth with one reply shape; precise NORMAL g
  replay, f rejection and DEMAND-layer control; run-3 observation and an
  uncapped report-retaining quiet suffix.

The parent package is the historical nested-STAR counterexample. Its old
policy and broken trace remain unchanged as controls. Dependency sources
are hash checked. Each declaration's transitive axioms are audited; only
`propext` and `Quot.sound` are allowed. No classical choice, custom axiom,
proof hole or external decision oracle is accepted.

The trace is a prefix-write/transparent-wrapper model, not a formalization
of the whole JVM. The tiny terminal controller records the existing
empty-DEMAND stop and cumulative reporting contract. Native cold tests
validate the execution bridge separately. The generic local preservation
proofs do not discharge the consolidated G1–G4 obligations or prove
termination of every program.

Five focused native tests include six cold scenarios: original native
positive, historical rejection, repaired relay, overwritten-field negative,
direct-call control and no-write control. The repair finishes naturally at
**run-3** with its NORMAL observation; the negative also stops at run-3.
The no-write control stops at run-1. The combined targeted suite has 65 tests.
Tests modify only a RunnerPort adapter. Production is unchanged, and no
project performance result or complete proposal integration is claimed.

```bash
python3 spec/lean/proposals/run2-star-relay-20261117/check.py \
  --out /tmp/run2-star-relay-proofs
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.NestedOverwriteStarAdmissionTest --offline
```

Use `--dependencies PATH` to reuse a source-hash-checked receipt from the
parent package. Compiled modules, logs, receipts and XML stay outside Git.

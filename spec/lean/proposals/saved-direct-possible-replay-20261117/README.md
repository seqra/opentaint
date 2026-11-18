# Possible DIRECT saved replay proof package

17 November 2026. Constructive Lean 4.35.0. Production unchanged.
Follow [proof-guide.md](../../../proof-guide.md).
[Repair contract and trace](../../../../docs/design/bidirectional-saved-direct-possible-replay-20261117.md).
[Consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).

**25 new claims; 7,237 cumulative audited claims in 420 checked modules.**

- `DirectPossibleReplay`: the latest unary prefix reference, adding only a
  possible DIRECT saved NORMAL FLOW read and its qualified ready-child
  routing. Current C2, paired C5, field limiters and handoff are reused.
- `RepairCases`: cold execution of the same historical and minimal programs.
- `DirectPossibleProofs` (25): literal preservation of old successful saved
  and routed replies; unchanged opposite/ineligible lanes; new replies D-only;
  no new NORMAL scalar result; arbitrary successful concrete prefix reply
  coverage with real E and fixed qualification; stored output heads/marks;
  one reply per existing scalar; cold fixed points and mandatory caps; the
  new run-4 guide and NORMAL run-5 observation; full165 repair and exact
  complete run-5 state equality for updated884; first-field E rejection;
  reuse of the constructive ready-child suffix cover.

The repaired minimal and full165 references have NORMAL observations and
empty demand at **run-5**. Six native component tests check both directions,
real E/mx/H, native paired C5 and final NORMAL application. Combined with
the earlier suite, **83 tests pass**. Production remains unchanged, so its
old broad-observation losses at run-5 remain expected-broken controls.
This is not whole-driver proposal integration.

The checker also executes two finite checks from
`scripts/demand_experiments/saved-direct-possible-replay-20261117/`:

- All 18 earlier ordinary cases reach within-run fixed points and natural
  completion. Double changes from run-13 to run-17; Growth from run-11 to
  run-13. The other completion runs are unchanged. This is a real workload
  cost, not an optimization claim.
- All 256 prefix/read/write cases match ordinary concrete execution:
  95 positive, 161 negative, no mismatch, natural completion through run-9,
  maximum 8 demand rows. The diagnostic bound is run-33.

These executable checks are not additional universal theorem claims.
The reference covers unary ordinary return cones, with FLOW conditional
queries and real concrete caller bindings. Typed Target/source-permission
scheduling, all ND/aliases/static paths, and all combined completion
histories are not modeled. G1–G4 remain open at whole-analyzer scope.
Every old parent proof keeps its original scope; the repair does not make
those proofs cover the entire combined engine.

```bash
python3 spec/lean/proposals/saved-direct-possible-replay-20261117/check.py \
  --out /tmp/saved-direct-possible-proofs
# Optional reuse of a source-hash-checked parent receipt:
#   --dependencies /path/to/ordinary-alignment-proof-output
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.SavedDirectPossibleReplayTest --offline
```

The checker validates all parent source hashes, compiles the new modules,
audits each theorem's transitive axioms, and executes both finite checks.
It permits only `propext` and `Quot.sound`, with no custom axiom, classical
choice, proof hole or external decision oracle. Compiled artifacts,
receipts, XML and large logs stay outside Git.

# Ordinary prefix-return soundness counterexample

17 November 2026. Constructive Lean 4.35.0. Production unchanged.
[Code, per-run trace, native controls and open obligation](../../../../docs/reports/bidirectional-prefix-return-soundness-gap-20261117.md).
[Current consolidated proposal](../../../../docs/design/bidirectional-demand-termination-approach-20261115.md).
Follow [proof-guide.md](../../../proof-guide.md).

**25 new claims; 7,212 cumulative audited claims in 417 checked modules.**

- `ConcretePaths` (5): definite concrete witnesses for historical cases 165
  and 884, including two compositions and the non-overwritten observed point.
- `UpdatedReplay` (definitions): the positive unary prefix machine with the
  latest `Run2Relay` C2. It retains ordinary moves/keeps, own prepared C5,
  field caps, NE and direction-qualified saved replay. No repair is enabled.
- `ReplayCases` (definitions): full historical CFG-return cones, the minimal
  straight-line one-call body, and actual guidance projection of MUST/mx.
- `MinimalGap` (20): all five cold within-run fixed points; demand frontiers;
  actual stored NORMAL helper; real mandatory cut; missing observed child;
  same-direction STAR rejection; empty current callee demand; run-4/run-5
  loss; unchanged masks/protection/caps; no outer replay at any larger limit;
  and an updated 884 NORMAL positive at run-5.

The model keeps both caller and callee within-run closure. It grants the
backward observation and original forward source even after service is
lost. The failed route therefore does not rely on a missing source seed or
an arbitrary finite iteration cutoff. Its terminal all-limit lemmas are
about empty outer demand/return service; they are not a whole-JVM iteration
semantics theorem. The native cold driver independently stops at **run-5**
with no finding for the minimal broad observation. An exact g.g.f control
retains the NORMAL finding at run-5. No loops, recursion, cleaners, ND,
static, aliases or configured pass rules occur in the minimal example.

Seven native tests include six cold executions and one direct matcher
control. Full case 165 reproduces the same broad-observation loss. Both
case 884 controls retain their findings at run-5. The suite uses
IncreasingLimits without a count cutoff. No prototype adapter is installed.
The combined targeted suite passes 77 tests, including the expected-broken
diagnostics; this is evidence for the open gap, not a correctness milestone.

```bash
python3 spec/lean/proposals/ordinary-alignment-audit-20261117/check.py \
  --out /tmp/ordinary-alignment-proofs
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.OrdinaryAlignmentSoundnessTest --offline
```

The checker source-hash-validates its dependency receipt, compiles the new
modules and audits each theorem's transitive axioms. Only `propext` and
`Quot.sound` are permitted. Logs, XML, JSON and compiled modules stay outside
Git. A changed saved-service rule requires a separate design/proof; this
package does not silently select one.

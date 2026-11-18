# Synthetic nested-call recurrence

Started 14 November; checked 15 November 2026. No production changes.

The [report](../../../../docs/reports/bidirectional-nested-saved-replay-nontermination-20261115.md)
contains ordinary Java, the two configured marking/observation rules and
complete relevant direction-sensitive run annotations. The sample has no
program loops, recursion, cleaners, special pass rules or library-MAY model.
It keeps the specified saved NORMAL replay policy unchanged.

| Module | Checked scope |
| --- | --- |
| `SavedReplayCycle.lean` | Complete mature paired C2/C5 packets; child queries; ineligibility for MUST/NE retirement |
| `StablePackets.lean` | Those packets at every limit >= 8; unchanged nonempty handoff by induction |
| `ColdMachine.lean` | Executable positive unary AP reference with two owners, three calls, normal records, queue closure and proposed compactions |
| `ColdCertificates.lean` | Cold run-1 through run-9 from empty stores; every complete state, quiescence and handoff |
| `CallerClosure.lean` | Exact caller offer domains, complete replies, backwards producer reachability, no later global cuts |
| `TargetClosure.lean` | Existing paired ZERO/Target C5, fresh forward/backward Target witnesses and continuation |

`TargetClosure` imports the existing `TargetZeroKernel`; the new model adds
no seed, Target bypass or NORMAL-to-DEMAND report conversion. The checker
also audits every theorem in that reused kernel. Its old reference-only
promotion helpers are not used by the new proof.

Use a fresh output directory outside the repository:

```sh
python3 spec/lean/proposals/nested-saved-replay-cycle-20261114/check.py \
  --out /tmp/nested-replay-proof-fresh
```

The checker first rechecks the previous proposal packages, then compiles
the reused Target kernel and every new module. It audits theorem axioms;
custom axioms, Classical dependencies, holes and `native_decide` are rejected.
Only Lean's `propext` and `Quot.sound` are allowed. The final receipt has
69 new theorems and 542 audited declarations across 32 modules, including
72 reused Target-kernel declarations. Legacy deprecated-name
warnings are disabled for the unchanged Target kernel only.

`generate_cold_certificates.py` in the search directory generates proposed
cold witness literals. Python output is not trusted: each literal is checked
with kernel `decide` against `ColdMachine`. `capture_nested.py` records the
exploratory run-31 trace outside the repo. `render_nested_report.py` renders
the per-run annotations; it is not a proof checker.

This is a scoped AP design proof, not full IR/binary correspondence. Three
native component tests separately verify the actual saved-opposite matcher,
real f.g input rejection and precise child service. The non-empty-MAY
proposal has no integrated production implementation to run uncapped.

Latest reached: exploratory **run-31**; kernel cold trace **run-9**;
stationary packets **run-9/run-10**, with an uncapped induction. Native
operators use field limit 8 (run-9 geometry), not a completed native run-9.

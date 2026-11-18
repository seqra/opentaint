# NORMAL uniform actual DATA coverage

Forward FULL DATA only. A retained, already applied NORMAL MUST can cover
the entire region of a concrete DEMAND EXACT/MUST/MAY/NE at the same owned
continuation and original premise, with equal mark and literal H. Keep
backward delivery, correlated STAR/FLOW and GROUP mode unchanged.

[Design, examples, all run results and safety limits](../../../../docs/reports/bidirectional-normal-uniform-actual-coverage-20261116.md).
Production is unchanged. Latest native diagnostic: **run-31**. The new
reference naturally stops at **run-5**; the largest old reference reaches
**run-15**. No finite cutoff proves natural termination.

| Module | Proof scope |
|---|---|
| UniformActual | Executable whole-region predicate; real E, context/H, retained NORMAL witness, order/idempotence, subset/work and negative cases. |
| UniformSafety | Every possible refinement point and finite concrete continuation remains supported; complete binding points, fixed-plan query bound and genuine cut. |
| UniformReplay | Earlier ordinary-code reference with the DATA filter at existing post-operation points; primitive transfers/C2/C5 unchanged. |
| UniformCampaign | Shared case/state data and final-DATA-only diagnostic helper; it is not the selected Target controller. |
| UniformCold* | Frozen DATA witnesses, publication/persistence and quiescence. Their final-DATA-only controller is diagnostic scaffolding. |
| UniformSticky / UniformStickyCold* | Selected cold controller and all 19 cold cases. Accumulate Targets from every within-run delivery, retain effects after late DATA coverage, and prove uncapped natural stops. |
| UniformAlternating / UniformColdAlternating | Complete marked-return/control fragment for all four actions and three calls; both normal and uncertain initial families, strict native saved MUST views, raw C5 and qualified heads. Natural run-5 stop. |
| UniformStrict* | All three earlier concrete replay cases with their actual packet filter and source/report controls; run-5 stop and uncapped no revival. |
| UniformProtected | Earlier protected call basis and selected cleaner image stay unchanged; run-3 and run-1 results. |

The selected accumulating-Target trace is a complete cold execution of the marked-return/control
fragment, not just the earlier counterexample's lower-bound projection.
Unchanged NORMAL argument/ZERO identities are outside that fragment. The
ordinary-reference wrappers use their existing scoped AP operation models;
these proofs are not a whole-engine bisimulation or a native NE integration.

**1,286 new constructive claims; 3,723 audited claims across 170 modules.**
Only `propext` and `Quot.sound` are allowed. No custom axioms, holes, classical
choice, native_decide or external proof oracle.

```bash
python3 spec/lean/proposals/normal-must-actual-coverage-20261116/check.py \
  --out /tmp/normal-uniform-actual-proofs
```

`--dependencies DIR --reuse-checked` can reuse a completed proof build. All
source hashes are checked; new modules are compiled and axiom-audited.
Cold equalities are checked by Lean even though diagnostic exporters freeze
their witnesses. Each final no-revival theorem quantifies over all later
iterations. It does not use an exporter horizon as a premise.

The frozen states and their proof terms are in this directory. Diagnostic
exporters and the freezer are under
[scripts/demand_experiments/normal-must-actual-coverage](../../../../scripts/demand_experiments/normal-must-actual-coverage).
They are not trusted proof inputs. Bulk logs and compiled output stay outside
the repository. Ten new native adapter tests plus ten controls pass.

The final-DATA-only observer was rejected for control use: it can forget an
earlier DemandTarget after late NORMAL coverage. The selected `UniformSticky`
controller preserves such effects. It reuses data witnesses where an exact
alignment proof succeeds and reconstructs the affected states otherwise.
Natural-stop claims refer to `UniformStickyCold*`, not that diagnostic helper.

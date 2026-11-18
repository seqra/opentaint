# R35/R36 cleaner progress: proof and search dossier

17 November 2026. Lean **4.35.0**. Production stays unchanged.
Follow [proof-guide.md](../../../proof-guide.md).
[Full counterexamples, per-run traces, rules and workload bounds](../../../../docs/reports/bidirectional-cleaner-termination-campaign-20261117.md).

## Checked models

| Module | New claims | Contract |
|---|---:|---|
| `DescendantCleanerCycle` | 20 | Cold EXACT-descendant Target recurrence, every uncapped run pair; computed empty-body identity; existing repairs inactive |
| `ExactMUSTClosure` | 13 | Projection closure of the selected point-cleaner/MUST coarsening; one output; natural run-1 |
| `UniformCleanerSpine` | 16 | Arbitrary cleaner path/E/point: exact whole/BELOW residual, linear row count, configured-prefix heads |
| `NestedCleanerProtocol` | 13 | Current nested-cleaner uncapped recurrence; repaired ALL/BELOW protocol, unchanged run-1, real cuts, natural run-3 |
| `CleanerSearch` | 1 | Executable finite local-cleaner model and checked operation boundary |

The checker audits **63 new claims**, plus the **7,245-claim, 422-module**
source-hash-checked parent closure: **7,308 claims in 427 modules**. Only
`propext` and `Quot.sound` may occur in transitive axiom dependencies.
All existence witnesses are executable; no classical choice, proof gap,
custom axiom or native decision shortcut is permitted.

## Fresh finite search

`CleanerSearch.main` checks **56,700 pipelines and 2,551,500 observations**:
two fields; source EXACT/MUST paths through depth 2; two cleaner paths
through depth 3; selected EXACT/ALL/BELOW; EXACT/MAY/NE observations through
depth 3; and membership words through depth 5. Half the sources are ordinary
Empty-E marking cases, and half are nonempty-E component inputs. Do not
interpret the latter as nonempty-E source actions during run-1.

It finds no further recurrence or lost required exact observation. Latest
natural completion is **run-5**. The maximum residual size is seven. It
checks the selected R35 coarsening against its own membership oracle and
preserves all actual retained marked points. The Target protocol retains
both NORMAL and DEMAND witnesses and checks backward marking permission;
it does not use DATA-only stopping. RemoveAll/ALL has the same scalar
spatial operation and separate native controls.

This scope has one local and no conditional marking, ND, ordinary intermethod
DATA query, aliases, statics or GROUP. Prior reference/native scopes remain
in the dependency closure. Finite search does not prove general termination
or whole-program absence of missed observations. Production does not yet
implement the consolidated proposal.

## Reproduce

Use an external output directory under the [data policy](../../../../docs/reports/EXTERNAL_DATA.md):

```bash
python3 spec/lean/proposals/uniform-cleaner-spine-20261117/check.py \
  --dependencies /path/to/post-direct-soundness-20261117/proofs \
  --out /path/to/uniform-cleaner-spine-20261117/checked-proofs
```

The parent must contain `receipt.json` and its compiled, source-identical
modules. If absent, run the parent's
[checker](../post-direct-soundness-audit-20261117/check.py) first. The new
checker revalidates every parent source hash, compiles all five new modules,
audits each claim's axioms and executes the fresh search. It rejects stale
models, incomplete output, gaps, warnings and nonzero search failures.

Native proposal components and current-engine controls:

```bash
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.DescendantCleanerTerminationTest \
  --tests org.opentaint.dataflow.bidi.ExactUniformCleanerClosureTest \
  --tests org.opentaint.dataflow.bidi.UniformCleanerSpineTest --offline
```

These **19 new tests** and the previous **92** targeted tests all pass
(**111 total**). They include expected-broken current-engine diagnostics
through **run-15/POLICY**. R35/R36 scalar adapters exercise the native AP
representation and normal operations; they do not replace production
transfers or run the complete proposed analyzer. The existing native
global-cut operation uses MAY, while the formal selected contract uses NE.
Tests require DEMAND at a real cut and do not mislabel that tail difference
as integration. Earlier cold controls naturally reach **run-9**.

External frozen artifacts: `uniform-cleaner-spine-20261117/checked-proofs/`
contains the cumulative receipt, compiled models and per-claim axiom logs;
`native/` contains Gradle output, 111-test XML and source hashes. All proof
and search source code is in this repository.

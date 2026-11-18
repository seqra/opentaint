# Nested field-path search and proof

The [proposal](../../../../docs/design/bidirectional-nested-field-goal-service-20261117.md)
uses one regular word language and one nested clause grammar. The
[report](../../../../docs/reports/bidirectional-two-sided-field-search-20261117.md)
contains ordinary code, cold traces, the native comparison, and the
limits of the model.

| Module | Claims | Checked result |
| --- | ---: | --- |
| PairedContext | 10 | A checked closed set contains every derivable state pair. It cannot prove a real shared word absent, including when an outer suffix follows recursion. |
| TwoSidedSearch | 1 | Actual cold C2, body, C5 and replay preserve the first two Target and marking transitions and reproduce the forward repeat at run-3. |
| LaneProof | 15 | Ordinary transfer and bounded C2/C5 steps, h branch separation at a g selector, the clean return cone recurrence, and quiet suffix after certified retirement. |

The per-pair induction uses eligible NORMAL and prepared-child providers
from the retained-service contract. The finite paired engine search checks
fixed points for the actual enumerated inputs. Whole native retention at
every depth is a separate obligation. The certificate proof itself holds
for arbitrary derivations in the complete grammar.

Use Lean 4.35.0. The checker pins all 445 parent sources. It compiles the
new modules and audits every theorem's transitive axioms. The audit permits
only `propext` and `Quot.sound`.

```sh
python3 spec/lean/proposals/two-sided-field-cycle-20261117/check.py \
  --dependencies /absolute/external-data/branching-field-cycle-20261117/checked-proofs \
  --out /absolute/external-data/two-sided-field-cycle-20261117/checked-proofs
```

Expected executable results:

```text
TWO_SIDED_CERTIFICATES total=882 disagreements=0
TWO_SIDED_SEARCH total=72 latestNatural=11 unfinished=0 noRouteWithNormal=0 possibleWithoutNormal=0
```

The test adapter changes only the eligible root Target in the handoff.
Run its controls with:

```sh
./core/gradlew -p core :opentaint-dataflow-core:opentaint-dataflow:test --offline \
  --tests '*WordChunkWriteReadTerminationTest' --tests '*NestedFieldPathCertificateTest'
```

The positive which requires the nested branch gets its NORMAL observation
at natural run-5 in baseline and adapter. The disjoint baseline reaches
run-9/POLICY and the adapter stops at natural run-5. Earlier loop and other
recursive fixtures are included in the combined suite.

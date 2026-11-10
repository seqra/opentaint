# NORMAL replay coverage for FLOW demand retirement

This package supports [the proposal](../../../normal-backed-flow-demand-retirement.md).
It changes no production code. OWASP's latest reached, completed and accepted
iteration remains **run-11**.

## Scope of the proof

`NormalBackedDemand.lean` defines an executable certificate checker P. A
certificate must cover **every** paired origin row. Native rows retain their
real direct/opposite role. Only opposite replay can justify a reader below
a STAR entry. Same-direction coverage needs an applicable prefix.

The 14 generic laws include:

- paired prefix specialization and reversal;
- a retained native witness for every checked origin;
- preservation of the represented concrete boundary transfers;
- preservation of caller boundary paths in an arbitrary surrounding CFG;
- rejection of an unavailable deeper direct reader and of an uncovered
  second origin merged into the same displayed MAY edge.

`ObservedCertificates.lean` is a standalone generated file. It includes the
generic model and 34 executable certificates from OWASP runs 7–11. They
cover 124 clipped origin rows. The checker validates the concrete fields,
bases, native roles and shared suffixes for each row.

The prefix model deliberately has no cut-generated concrete effects. A MAY
debt represents work for its complete original copy relation; its arbitrary
extra suffix combinations are not new program behavior. The scope guard is
an adapter obligation, not a proof about arbitrary Kotlin objects. The source
check computes the finite copy graph from captured compiled forms. The
normal-prefix composition argument and observation separation are stated in
the proposal. No claim of a verified whole analyzer or universal termination
is made.

## Repeat the checks

From the repository root:

```sh
python3 spec/lean/proposals/normal-backed-demand-20261110/check.py \
  --output-directory /tmp/normal-backed-proof-check

python3 spec/lean/proposals/normal-backed-demand-20261110/check-copy-closure.py \
  --output-directory /tmp/normal-backed-copy-check

python3 spec/lean/proposals/normal-backed-demand-20261110/generate-observed.py \
  --closure /tmp/normal-backed-copy-check/copy-closure.json
```

From `spec/lean`:

```sh
lake env lean proposals/normal-backed-demand-20261110/NormalBackedDemand.lean
lake env lean proposals/normal-backed-demand-20261110/ObservedCertificates.lean
```

The toolchain is pinned by the parent `lean-toolchain`. The declared checks
compile without proof holes or custom/classical axioms. Printed dependencies
are limited to `propext` and `Quot.sound`.

`NormalBackedDemandReplayProbeTest.kt` is an archived native probe, not a
production test-source change. It was supplied to Gradle through an external
init script. One test checks 60 legal input geometry/mark/layer combinations
against the current micro-edge operation. It separately checks rejection of
the broad STAR input under SAVED_DIRECT and admission under SAVED_OPPOSITE.

To repeat that probe from `core`, use only Gradle:

```sh
./gradlew --no-daemon :opentaint-dataflow-core:opentaint-dataflow:test \
  -I ../spec/lean/proposals/normal-backed-demand-20261110/native-test.init.gradle \
  --tests org.opentaint.dataflow.bidi.NormalBackedDemandReplayProbeTest
```

## Evidence

[checks.json](checks.json) records source hashes, commands, axiom audits,
the native test result, and the proof limits. The
[data record](../../../../docs/reports/data/bidirectional-normal-backed-demand-20261110.json)
embeds the complete compiled forms, copy closure, native test source/init
script and receipts. The forms capture preserves all 2,633 finding locations.

The proposal has not been installed in C5 or handoff. There is no measured
retirement speedup or new early-stop result in these receipts.

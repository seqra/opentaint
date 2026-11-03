# Composition of the three selected designs

Status: **SELECTED DESIGN COMPOSITION; NOT IMPLEMENTED**.

This small package imports the three component models without changing
their data models or semantic contracts:

1. `joined-state-release-selected-design-20261103`;
2. `loop-consumer-query-reuse-20261103`;
3. `packed-static-guidance-20261103`.

`python3 check.py` verifies the pinned PASS receipts and their authenticated
inputs, compiles the exact component sources and [Composition.lean](Composition.lean),
then audits every explicit declaration in the composition module. It uses
one CPU and at most 900 MiB per Lean compiler process, with no parallel
compiler. No Gradle, analyzer, MAT, profiler, or Kotlin implementation runs.

The theorem composes conditional interface equalities. It does not promote
component models into a proof about Kotlin, GC behavior, report quality,
resource-limit outcomes, speed, or global analyzer convergence.

See [REPORT.md](REPORT.md) for the concrete integration contract and remaining
native adapter obligations. `component-pins.json` fixes the three receipts,
source modules, audits and detailed designs used by this check.

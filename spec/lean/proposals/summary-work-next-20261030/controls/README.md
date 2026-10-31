# Production-AP control for inherited cover pruning

This is a proposal control, outside the regular Gradle test source tree. It
checks the existing concrete TAINT algebra and protected delta semantics.
It does not install or verify the proposed cached-fold pruning algorithm.

From the repository root, run this command when project measurements are closed:

```sh
cd core
./gradlew \
  --init-script ../spec/lean/proposals/summary-work-next-20261030/controls/controls.init.gradle \
  --max-workers=1 \
  -Dorg.gradle.jvmargs=-Xmx1g \
  -Pkotlin.compiler.execution.strategy=in-process \
  :opentaint-dataflow-core:opentaint-dataflow:test \
  --tests org.opentaint.dataflow.bidi.InheritedCoverPruneTest
```

The init file resolves its source directory from its own file location. It
adds only this control source to the included core test project. It caps that
test process at 1 GB and one fork. No absolute workspace path is required.
Do not copy the same class into the regular test tree while using this init.

The test source is byte-identical to the external control already executed at
runtime commit `e090118e5f9603f1973c0578a3e04998035f4508`:

- The targeted run passed all 3 tests.
- The subsequent full suite passed 2,133 core tests and 452 JVM tests. The core
  count includes these 3 controls and the 4 return-image/universal-match controls.
- The new portable init file has not been executed. No additional Gradle or
  project run was made to prepare this package.

The preserved full-suite receipt is external campaign evidence:
`preparation/next-proposal-full-test-validation.json`, SHA-256
`fb897f2ec8314ae974ae7499a8a8661850e082dca19b6cb5b5533b5a95b9cd93`.
The source and archived XML hashes are in `hashes.json`. Hash equality binds
these tests to that receipt. It does not prove the new init's execution.

The controls check covered/uncovered folded payloads and the exception where
ordinary MAY coverage must retain a new protected EXACT dependency. Differential
FLOW, mixed-tail/E, shared DAG and cancellation tests remain implementation gates.
The associated project capture was Stirling run-6; the closed command reached
run-7, completed run-6 and accepted run-5.

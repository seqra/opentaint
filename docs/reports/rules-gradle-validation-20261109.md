# CI rules: local Gradle validation

9 November 2026. State: **CI POLICY PASS**, with two harness coverage limits.

The rule suite ran from the primary checkout through Gradle tasks. The analyzer,
autobuilder and Go server came from local source builds. No CI artifacts were
downloaded. The sample build, rule coverage check, analyzer and result gate all
passed. The [procedure](../rule-testing.md) gives the repeatable commands.

## Result

| Language | Declared samples | Successful | Disabled | Skipped | FP | FN | Uncollected |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Java | 377 | 353 | 22 | 0 | 0 | 0 | 2 |
| Go | 201 | 201 | 0 | 0 | 0 | 0 | 0 |
| Total | 578 | 554 | 22 | 0 | 0 | 0 | 2 |

The CI policy requires `skipped + falsePositive + falseNegative == 0`.
It allows disabled samples. All 576 collected entries are accounted for. The
22 disabled Java samples belong to 11 disabled rules. All 201 declared Go
samples were collected and passed. There were no extra result entries.

The analyzer and the JSON gate completed with exit code zero. A separate
synthetic result with one false negative made `checkRuleTestResults` fail with
exit code one, as required. This fixture did not alter the real result or rerun
the analyzer. The real false-negative count remains zero.

## Source and execution

Source revision: `e480321794bde6a6225db50edef630b0d6de769c`.
Core tree: `8b38a03586138acbbf5aaadd94b5fb301d6c9cad`.
The core, rule definitions and sample sources have no uncommitted changes.
Only validation documentation, its init script and pipeline instructions were
added. No analyzer semantics were changed.

The source-built portable project contains one Java project and one Go
project. Java compilation and dependency resolution both completed. The run
used JDK 17, an 8 GiB analyzer heap, batch size 2,000, disabled multi-release
JAR loading, all rule severities and `--debug-run-rule-tests`, as specified by
the workflow's analysis step.

| Step | Task | Result | Gradle-reported duration |
| --- | --- | --- | --- |
| Samples and coverage | `:build :checkRulesCoverage` in `rules/test` | PASS | 9 s |
| Go server | `:opentaint-ir:go:buildGoServer` in `core` | PASS | 14 s |
| Portable model | `:opentaint-jvm-autobuilder:runAutoBuilder` in `core` | PASS | 28 s |
| Analysis and JSON gate | `:runProjectAnalyzer :checkRuleTestResults` in `core` | PASS | 1 min |

The project start/end log intervals are 44.931 seconds for Java and 4.478
seconds for Go. These include each project's loading, sample analysis and
report generation. The Gradle duration also includes task setup and build
dependencies. No timeout or OOM ended the run.

**Latest reached bidirectional iteration: not applicable.** The rule runner
uses a separate legacy analysis per sample. It does not run the alternating
iteration driver, and the log has no `BIDI_RUN_START` marker.

## Limit 1: the Java rule runner does not select the new core

`TestProjectAnalyzer.analyzeTestSample` constructs `JIRTaintAnalyzer` without
the `bidiPolicy` argument. Its default is `null`. The ordinary project runner
sets this policy when `--ifds-bidirectional` is selected; the rule runner does
not. The flag can change Spring setup without selecting the new core.

Thus, this test adds the workflow's default-engine rule gate to validation.
It does not replace the native bidirectional tests or the
[bidirectional project validation](bidirectional-post-merge-project-validation-20261109.md).
No flag-only second run is presented as a bidirectional rule test.

## Limit 2: two interface samples disappear before result classification

The Java sample manifest declares these entries for
`java/security/unsafe-deserialization.yaml#server-dangerous-object-deserialization`:

| Expected kind | Entry |
| --- | --- |
| Positive | `security.unsafedeserialization.UnsafeDeserializationSamples$DangerousRemoteService#invoke` |
| Negative | `security.unsafedeserialization.UnsafeDeserializationSamples$SafeRemoteService#invokeById` |

Both classes are interfaces. `TestProjectAnalyzer.resolveMethods` rejects
interfaces, abstract classes and anonymous classes. `resolveSamples` then
returns no sample. The log confirms both omissions:

```text
No sample found for ...UnsafeDeserializationSamples$DangerousRemoteService#invoke (mode=default) in this module
No sample found for ...UnsafeDeserializationSamples$SafeRemoteService#invokeById (mode=default) in this module
```

Neither entry reaches `success`, `disabled`, `skipped`, `falsePositive` or
`falseNegative`. The metadata coverage check passes because a test declaration
exists for the rule. The CI result gate passes because the missing entries are
not counted as skipped. These two entries are a collection gap, not successful
tests. This validation records the gap and does not change the harness's sample
resolution policy.

## Tools and dependency preparation

The first offline sample build failed because third-party JARs were absent
from the cache. Normal Gradle resolution restored the build. A Go build with
`GOPROXY=off` also failed because required module metadata was absent. Normal
Go module resolution restored that source build. These were preparation
failures, before the successful analyzer run. This is not a zero-network claim.

The installed system tools were Go 1.25.5 and protoc 3.6.1. The source requires
Go 1.26.0 and proto3 optional-field support. Cached Go 1.26.1 and protoc 25.1
were selected through a private tools directory. `BASH_ENV` preserved this
selection inside the Go task's `bash -lc`. No system tools were replaced.

The workflow's JDK 11 analyzer build setting also conflicts with the current
Java 17 target. The local procedure states the actual source requirements.
The workflow file itself was not changed.

## Pipeline and evidence

`task.md` now requires this rules gate. The rules README links to the
[Gradle procedure](../rule-testing.md) and uses the actual coverage task path.
`scripts/rule-tests.init.gradle` adds an opt-in JSON gate; it does not alter the
analyzer task's JVM settings, arguments or runtime code.

The [data packet](data/rules-gradle-validation-20261109.json) contains the full
real test results, collection audit, source/tool hashes, model hash, command
arguments and log receipts. Raw outputs are retained at:

    /drive-testcomp/opentaint-go-rules/rules-gradle-validation-20261109

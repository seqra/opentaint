# Bidirectional rule-test runner validation

9 November 2026. State: **RUNNER FIX VERIFIED; RULE SUITE NOT ACCEPTED**.

The Java rule-test runner now honors `--ifds-bidirectional`. It uses the same
configured iteration policy as the ordinary project analyzer. Without the flag,
it keeps the legacy engine. Go samples keep their existing engine.

The full validation exposed two convergence failures. Expected sample results
match the legacy suite, but the analyzer does not complete successfully. A zero
false-negative count alone is insufficient to accept this run.

## Implementation and regression

Implementation revision: `e3c70dabc60a906250a91ed9ed738f2ca9e50182`.

The runtime change in `TestProjectAnalyzer` is:

```kotlin
bidiPolicy = if (options.ifdsBidirectional) configuredIncreasingLimits() else null
```

A `RULE_TEST_START` log line identifies each Java sample and selected engine.
Validation then checks real `BIDI_RUN_START` and `BIDI_ANALYSIS_END` events.
It does not treat the engine label as proof. The dataflow-core and JVM-dataflow
Git trees are unchanged. No transfer, mark, field, demand, summary or stop
algorithm was modified.

`RuleTestEngineSelectionTest` uses the real rule runner and the existing
`SimpleDataFlowSample`. It checks both flag values, requires the source-to-sink
finding, and checks driver events. Before the fix, the legacy control passes
and the flag-enabled case fails because no bidirectional driver runs. After the
fix, both cases pass, with zero errors or skips.

The ordinary root test build is blocked by existing tests that still reference
removed `ReportState`, `SinkWitness` and related APIs. This failure occurred
before the production change. The new regression ran with a temporary init
script that selects only its Kotlin test source. No permanent exclusions were
added. The data packet retains that script and both XML results. A nonincremental
source build also resolved a local incremental-compile failure on existing
top-level symbols. The full root test suite is not claimed as passing.

## Default-budget attempt

The source-built Java/Go model from the previous Gradle validation was reused
unchanged. The analyzer ran through `:runProjectAnalyzer` with 8 GiB, FULL marks,
limits `1,1,2,3,...`, all rules and `--ifds-bidirectional`. No CI artifacts were
used. The default per-sample IFDS budget is 10,000 seconds.

The run completed 126 Java samples, then repeatedly refined
`InsecureDesignSamples#mixesTrustedAndUntrustedInSessionInsecure` for
`java/security/insecure-design.yaml:trust-boundary-violation`. It reached
**run-35700**, with no completed sample-level driver return. The process was
stopped with SIGTERM after the repeated pattern was established. No final test
JSON was produced. This is an interrupted attempt, not a completed CI result.

The sample has no source-code loop:

```java
public void mixesTrustedAndUntrustedInSessionInsecure(HttpServletRequest request) {
    String username = (String) request.getSession().getAttribute("username");
    String theme = request.getParameter("theme");
    request.getSession().setAttribute("userProfile", username + ":" + theme);
}
```

Later forward frontiers repeatedly have one demand edge, one Target demand,
one report and zero analysed methods. Backward frontiers have two demand edges,
one Target demand, one report and zero analysed methods. Field limits continue
to increase. This locates repeated work in refinement scheduling/guidance;
it does not show expensive method-body processing. Counts alone are not a
formal proof that all semantic state is unchanged or that termination is
impossible. No convergence was observed through the recorded iteration range.

## Bounded diagnostic

A separate run changed only the per-sample budget to 30 seconds, using the
existing `--ifds-analysis-timeout 30` option. This is a diagnostic configuration,
not a successful substitute for the default-budget validation.

All **353 collected Java samples** entered the actual bidirectional driver.
There are 351 COMPLETE sample analyses and two TIMEOUT analyses:

| Sample | Latest reached | Latest engine complete | Status |
| --- | --- | --- | --- |
| `security.insecuredesign.InsecureDesignSamples#mixesTrustedAndUntrustedInSessionInsecure` | run-11380 | run-11379 | TIMEOUT |
| `security.xss.XssHtmlResponseSpringSamples$SafeStringReturnController#safeStringReturn` | run-8336 | run-8335 | TIMEOUT |

The maximum reached label is **run-11380**. Each sample starts its own driver;
this label does not describe one shared suite iteration. The data packet gives
latest reached/complete labels and driver status for every Java sample.

The result JSON contains:

| Engine / language | Successful | Disabled | Skipped | FP | FN |
| --- | ---: | ---: | ---: | ---: | ---: |
| Bidirectional Java | 353 | 22 | 0 | 0 | 0 |
| Existing Go | 201 | 0 | 0 | 0 | 0 |
| Total | 554 | 22 | 0 | 0 | 0 |

The JSON classifications equal the complete previous legacy result JSON.
A timed-out analysis can retain an earlier finding, or return no finding for a
negative sample, and still be classified as successful by the test harness.
Therefore, these counts do not mean that every analysis passed. The analyzer
exits with code **254** for TIMEOUT; Gradle fails `runProjectAnalyzer` and does
not run the downstream JSON gate. The complete validation remains **failed**.

The two RMI interface declarations documented in the
[legacy report](rules-gradle-validation-20261109.md) remain uncollected. They
are not counted as successful or skipped samples. This runner update does not
change sample resolution.

## Reproduction and evidence

The [Gradle procedure](../rule-testing.md) now includes the bidirectional command.
`task.md` requires that flag and actual per-sample driver evidence. The CI
workflow's unflagged invocation still selects the legacy engine; this change
makes the existing flag work rather than changing its default.

The [data packet](data/bidirectional-rule-runner-validation-20261109.json)
contains both run audits, all diagnostic sample classifications, actual JVM
commands, source/model hashes, regression XML receipts and the default stop
receipt. Raw logs remain at:

    /drive-testcomp/opentaint-go-rules/rules-bidirectional-runner-20261109

The two convergence cases require a separate core investigation. No algorithm
fix or relaxed result policy is included in this runner change.

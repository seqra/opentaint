# Known failure: `CleanerDslAnalysisTest`, 2 of 20 cases

Recorded 2026-08-21, on the rebase of `saloed/base-only-clean` onto `origin/main@cbe3b3ffc`.

## What fails

`core/src/test/kotlin/org/opentaint/jvm/sast/dataflow/CleanerDslAnalysisTest.kt`

- `branch-specific cleaners do not clean the opposite alternative at a join`
- `nested helper AnyField cleaner removes a nested AnyField source`

Both fail on the **second** assertion, the no-cleaner control:

```text
The no-cleaner control must reach the same helper sink
  expected: <[helper-sink-sink]> but was: <[]>
```

The cleaning assertion in each test passes. What fails is the baseline: with cleaners
disabled the flow should be reported, and nothing is reported at all.

## What it is not

It is **not** a regression introduced by the rebase, and **not** related to the deep
accessor exclusion feature that came with the new base.

- `git bisect` over the rebased branch, with `origin/main` as good, names
  `feat(analyzer): stage analysis and select the full scan's rules from a shallow pass`
  as the first bad commit.
- `TaintAnalyzer.kt` is **byte-identical** before and after the rebase, so the
  responsible code was replayed unchanged.
- The test itself is new: it arrived with `a703d61a6` in the new base. This branch had
  never been run against it before.

So this is a pre-existing property of the staged pipeline that an upstream test now
exercises for the first time.

## Mechanism

`TaintAnalyzer.kt:143`, gate 1 of the three recall gates in the staged pipeline:

```kotlin
val (actionableRules, status) = shallowScan(analysisStart, entryPoints, startMethods)
if (actionableRules.isEmpty()) return emptyList<VulnerabilityWithTrace>() to status
```

The shallow pass runs under `BaseOnlyField`. For these two helper-call shapes it
discovers nothing, so the full scan never runs and the result set is empty regardless
of what the full scan would have found under `Tree`.

Confirmed by experiment: replacing that early return with a warning makes both tests
pass.

## Why it was not fixed here

The obvious fix — fall through to the full scan when the shallow pass finds nothing —
was tried and is **not safe as-is**. It fixes these two cases and breaks two others in
the same file:

- `AnyField sink hidden in a helper stays silent after cleaning`
- `helper source is cleaned before an AnyField sink`

Those two assert that cleaning leaves *no* finding. Running the full scan with an empty
actionable-rule set reports findings the cleaner should have removed, i.e. it trades two
false negatives for two false positives.

Gate 1 also exists for cost reasons: it is what stops a project with no shallow
discoveries from paying for a full scan. Changing it is a product decision that needs a
benchmark run, not a local test fix.

## If picking this up

Read the branch notes on the three recall gates first — gate 2 (a trace-resolution
failure permanently deleting a sink) has a better measured yield than gate 1 and a
narrower blast radius. Any change here must be measured on the e2e corpus, and finding
counts must be diffed on `(ruleId, path, line, cols)` rather than compared in aggregate.

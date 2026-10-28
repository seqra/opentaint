# Experiment: increase the field limit on every run

Date: 28 October 2026. Status: measured. See the
[iteration and frontier comparison](../reports/bidirectional-run-index-field-limits-performance-20261028.md).
The default remains `REPEAT_RUN1`.

Compare two schedules on the same four project inputs:

| Run | Direction | Current `REPEAT_RUN1` | Experiment `RUN_INDEX` |
|---|---|---:|---:|
| run-1 | Forward | 1 | 1 |
| run-2 | Backward | 1 | 2 |
| run-3 | Forward | 2 | 3 |
| run-4 | Backward | 3 | 4 |
| run-n, n > 1 | Alternating as before | n − 1 | n |

The only selected semantic change is the field budget on run-2 and later.
This can change facts, demands, convergence and findings. Equal run numbers
are not equal precision settings. At a fixed later limit, the two schedules
also have different directions. Do not call a time difference an isolated
implementation speedup.

The default stays `REPEAT_RUN1`. Select the experiment in the analyzer JVM:

```text
-Dopentaint.bidi.fieldLimitSchedule=RUN_INDEX
```

The project entry point reads the setting once and selects an immutable
policy. Every `RunConfig` retains and validates that schedule. Run-1 must use
limit 1. Invalid setting names and inconsistent configurations fail. Run
direction, FULL mark mode, stopping rules and the existing analysis budget
do not change.

## Required input validation change

The old run-2 static validator checks `path.size == 2`, because the old budget
permits the class anchor plus one field. With limit 2, `C.f.g/T` can be a legal
bounded actual input or seed. Apply the selected current limit to this check:

```kotlin
namedFieldAnchor(actual) &&
actual.path.drop(1).all { it.isCounted() } &&
actual.path.count { it.isCounted() } <= currentFieldLimit
```

The class anchor does not count. Field and element accessors count. Keep the
existing EXACT/ANY/STAR and exclusion checks. Keep the EXACT class marker
case. Continue to reject broad root/class concrete marks and backward MUST
inputs. The existing field cut still runs before validation. The validator
does not create initials or authorize a source/sink literal shape.

Both normal input admission and backward sink-seed admission pass the current
limit. At limit 1, the accepted named-field grammar is unchanged. Run-1
initial shapes remain unchanged.

## Behavior kept unchanged

Demand storage still uses special transitive static lookup only for incoming
run-2. Incoming run-3 and later use local lookup. A larger run-2 budget does
not extend the static completion lifetime.

All AP transfer/intersection rules, field and mark exclusions, FLOW subsumption,
protection, rules, static pool supply, summary persistence, predefined method
models and call handling remain as before. No next-iteration optimization
from the performance proposal is included.

## Evidence and checks

The constructive [schedule model](../../spec/lean/ApSpec/RunIndexFieldLimitExperiment.lean)
proves positive limits, first limit 1, the unchanged default, nondecreasing
limits and strict growth for `RUN_INDEX`. Direction and mark-mode selection
do not depend on the schedule. Its owned declarations have empty axiom sets.
It does not prove AP equivalence, termination or a performance bound.

Tests check the flag and unchanged default, exact config validation, policy
capture across real barriers, depth-2 static input/seed admission, demand
intersection with prior coarse geometry, and local-only demand after run-2.
The measurement helper checks that only the schedule property differs.

Reuse the saved current campaign at runtime `2273c8245` from
[the current report](../reports/bidirectional-demand-storage-predefined-performance-20261028.md).
Do not rerun that campaign or the legacy `f945f92` baseline. Keep the four
heaps and timeouts, FULL, static propagation and alias settings. Use Gradle
`runProjectAnalyzer`, profiles and automatic OOM snapshots as before. Do not
add a manual heap pause to the experiment.

For each project compare all `Iteration times and demand frontiers` rows.
Include direction, actual field limit, status, engine seconds, joined seconds,
barrier seconds and outgoing demand memberships. Include reached, completed
and accepted forward iterations. Compare resource outcome and strict result
identities as checks on the changed precision schedule. Keep engine times
separate from the run-1 joined phase and capture pauses.

The experiment root is
`/drive-testcomp/opentaint-go-rules/run-index-field-limits-20261028`.
Preserve saved-current compact data and hashes before removing its old raw
captures. Record cleanup, input audits, source pin, commands and final output
bindings in the experiment receipts.

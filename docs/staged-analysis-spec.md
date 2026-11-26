# Staged analysis specification

The implementation is a clean reconstruction of the BaseOnly prototype.

## BaseOnly access domain

BaseOnly is a finite over-approximation of the Tree access-path domain. A
projected access contains an optional static accessor, at most one structural
accessor, and one terminal or abstraction marker. BaseOnly erases field
identity; BaseOnlyField retains the outermost field or element.

Projection, reads, clears, concatenation, exclusions, summaries, and
subscriptions may add represented paths but must not remove a path represented
by Tree. The law and Tree-differential tests are the executable contract. A
small constructive model is in `formal/staged-analysis/BaseOnly.lean`.

## Analysis phases

The analyzer delegates phase control to `StagedAnalysisRunner`:

1. Prescan discovers relevant rule identifiers with the existing Tree-based
   analysis.
2. Shallow scan uses BaseOnlyField by default and confirms candidate sinks.
3. Exact rule discovery resolves each candidate's trace and collects only the
   source, transformation, and sink actions on that trace.
4. Full scan uses the configured precise AP domain and the exact selection.

Exact trace resolution and rule discovery share a small per-candidate
processing-time budget (10 seconds by default).

During the shallow phase, zero and class-static facts use an empty method
context. Other facts retain exact contexts. Lambda and functional-interface
constraints are never erased because their concrete type may affect dispatch.
Trace lookup applies the same normalization so it can find the shared shallow
summaries.

Selection is fail-open. Any incomplete shallow analysis, confirmation, trace
resolution, rule search, or empty result produces no exact selection. With no
exact selection installed, the full-scan provider retains the prescan's
established method-level selection. Cleaners, pass-through rules, and
static-field sources also remain delegated because they are not statement-level
trace selections.

No forward-action fallback, direct sink index, IFDS worklist quotient, or JVM
resolution cache is part of this implementation.

## Recall obligation

Let `R_m` be the method-level rules selected by the prescan and `select(P)` the
rules collected from a completed set of shallow traces `P`. The runtime plan
is:

```text
plan(P) = restricted(select(P))  when every discovery is complete
          baseline(R_m)          otherwise
```

For the restricted case, every precise witness represented by a confirmed
BaseOnly trace must have all of its source, transformation, and sink rules in
`select(P)`. For every other case, method-level execution makes the result
identical to the established baseline full scan. The fail-open part is modeled
in `formal/staged-analysis/StagedAnalysis.lean`.

## Verification

```text
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --tests 'org.opentaint.dataflow.ap.ifds.access.baseonly.*'
./gradlew :opentaint-dataflow-core:opentaint-dataflow:test --tests 'org.opentaint.dataflow.ap.ifds.trace.ExactProcessingTimeBudgetTest'
./gradlew :test --tests 'org.opentaint.jvm.sast.dataflow.ThingsBoardEntityActionExplosionTest'
./gradlew test
```

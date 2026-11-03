# Implementation: keep NORMAL ND contributors

Date: 3 November 2026. Implement
[normal-nd-contributors.md](../../spec/normal-nd-contributors.md).
Follow [proof-guide.md](../../spec/proof-guide.md) and
[impl-proposal-guide.md](../../spec/impl-proposal-guide.md).

## 1. Result and semantic scope

Keep a NORMAL conditional edge that satisfies a leaf of a multi-input rule.
Use that edge again at the same rule point in a later forward run. Keep
incomplete conditions too. Do not retain DEMAND evidence.

```text
before: local join leaves die when a run freezes
after:  NORMAL leaf edges survive; the ordinary join can use them again
```

This is a selected change to rule-evidence persistence. It does not change
method or block ZERO admission, C2, C5, field transfer, source permissions,
complete ND caller matching, or Target composition. The separate forward
internal ZERO-control draft is not part of this implementation.

## 2. Capture and key

Add `store/NormalRuleContributorStore.kt`. A row names a condition point
and an accepted leaf input. It does not contain compiled rule objects.

```kotlin
data class NormalRuleContributorRow(
    val owner: Owner, // MethodKey + BlockScope + MarkMode.
    val rule: NormalRuleDescriptor,
    val site: StableRuleSite,
    val leaf: Int,
    val input: ConjunctionStore.Input,
)

// input.layer == NORMAL && input.facts!!.layer == NORMAL.
// input.premise is the complete original conditional premise.
```

Use a stable rule occurrence for predicate sources and sinks. Use immutable
literal/target values for a legacy conjunctive transfer. Use the original
sink identity, alternative, and patterns for a legacy sink. Keep these
families separate. Do not retain a `RulePredicate`, `SourceRuleOccurrence`,
`SinkRule`, `ConjunctiveEdge`, callback, actor, or call plan in the row.

The stable site keeps the physical instruction, call stage, action and
substep, site kind, boundary side, and cleaner phase where present.
`BlockRunState.operation()` creates a transient `FormOwner`; that transient
owner must not make the point different in the next run. Keep the actual
block entry port. Do not canonicalize it to another physical port.

Use the semantic observation phase for call sinks. They are checked at
BOUND. Normal execution names its first outgoing stage; a resumed check
can name another outgoing stage. Normalize these two sink addresses to
BOUND in the cache key only. Do not change the real request/resume site.
Sources and legacy conjunctive transfers keep their separate stages.

Use this same semantic site as the namespace for FULL local condition
stores, including run-1 origin stores. The current rule-plus-statement
key can otherwise mix two source phases after restoration. This is an
explicit ownership correction. Keep call-summary E6 state separate and
unchanged. Keep GROUP live condition stores unchanged.

Capture after `MarkCheck.Holds`, before inserting into the ordinary join:

```kotlin
if (checked.facts.layer == NORMAL) {
    temporary.keep(rule, at.site, leaf,
        ConjunctionStore.Input(premise, NORMAL, checked.facts))
}
```

Use this at `conjunctionAt`, source `multiLeaf`, predicate sinks, and legacy
conjunctive sinks. Keep unary transfers and cleaners unchanged. Current
cleaner lowering does not provide a multi-mark condition evaluator; do not
add one here.

## 3. Persistent storage and barrier

```kotlin
class SharedObjects(...) {
    val normalRuleContributors = NormalRuleContributorStore(ap)
}

class NormalRuleContributorStore(ap: ApManager) {
    fun snapshot(): NormalRuleContributorView
    fun publish(rows: Iterable<NormalRuleContributorRow>)
}
```

The snapshot is read-only. An actor has its own temporary collector and
restore-once set. Use existing AP union operations to merge Facts with
the same point, leaf, full premise, and fact group. Preserve protection,
exclusions, field geometry and marks. Do not alter equality to hide a
premise or a metadata difference.

At actor freeze, export the temporary immutable rows. The original method
actor also exports all entered child-block rows. After a complete forward
run, publish these rows at the driver barrier. Build a complete next
snapshot before making it visible. Cancelled or failed runs publish no
new partial snapshot. Keep earlier rows when a later run skips an owner.

Backward runs neither restore nor publish these forward certificates.
Implement capture and restore for FULL mode. Skip both for GROUP mode;
its existing known issues remain outside this correction. Keep mode in
the key. Do not turn an old group certificate into a full-mark certificate.

## 4. Restore with the existing join

Add `engine/NormalRuleContributors.kt` for point normalization, local
capture, and restore-once bookkeeping.

```kotlin
class NormalRuleContributors(...) {
    fun restoreOnce(rule, site, replay: (NormalRuleContributorRow) -> Unit)
    fun keep(rule, site, leaf, input)
    fun freezeRows(): List<NormalRuleContributorRow>
}
```

Call restoration only after a current input has satisfied a leaf of this
rule. A nonmatching check cannot activate saved evidence.

```kotlin
fun <Binding> acceptedLeaf(rule, site, leaf, input, add, emit) {
    val ready = mutableListOf<Binding>()
    contributors.restoreOnce(rule, site) { saved ->
        add(saved.leaf, saved.input) { ready += it }
    }
    // Existing join dedup has now recorded these complete bindings.
    // Deliver them once at this real accepted check.
    ready.forEach(emit)

    contributors.keep(rule, site, leaf, input) // NORMAL only.
    add(leaf, input, emit)
}
```

`add` is the existing `RulePredicateStore.add`, `addBinding`, or
`ConjunctionStore.addBinding` operation. This preserves NNF branch choices,
full AND requirements, fact merging, and per-run deduplication. Do not
persist join DAGs, complete products, or the prior emitted set.

Run-1 keeps its current origin-splitting procedure. It only captures new
NORMAL evidence for later runs. It has no previous evidence to restore.

Source completion uses the current callback, including the existing source
seed check. Sink completion uses the existing witness code. Saved facts
must not be added to `Triggers.parts`; that list describes the current
input and also controls boundary metadata effects.

## 5. Complete premises and Targets

```text
saved   P -> x/T  NORMAL
current Q -> y/U  DEMAND

CM(x,T) AND CM(y,U):
    {P,Q} -> DemandTarget
```

Keep every member of P and Q. A caller with only Q cannot apply this row.
If all contributors are NORMAL, use the existing NormalTarget result and
its NORMAL-only application. Existing saved NormalTarget suppression
still applies. No Target is emitted during snapshot publication.

For the session regression:

```text
saved:   ZERO -> session.$/SESSION   NORMAL
current: I    -> param.$/DATA        NORMAL
result:  I    -> NormalTarget(id)    NORMAL
```

There is no new independent ZERO arm. The session evidence stays local to
the same sink condition; it is not an input fact for other instructions.

For a newly completed ND row, the existing handoff selects the full
multi-premise relation even when its layer is NORMAL. This can guide a
later run if a current caller lacks a complete binding. Keep this existing
handoff and call policy unchanged.

## 6. Proof and test sequence

First check the constructive model in
`spec/lean/proposals/normal-nd-contributors-20261103/`. Check premise union,
layers, exact-key isolation, incomplete evidence, activation, deduplication,
metadata identity, and the SESSION/DATA witness. Model proofs cover these
relation laws; they do not verify the Kotlin matcher or scheduler.

Then implement the collector and service integration. The existing native
`LoopBlockTrustBoundaryFindingTest` supplies the failing regression. Keep
its exact source rules and finding assertion unchanged. Add focused tests
for old conditional nonzero premises, incomplete conditions, bad callers,
DEMAND rejection, FULL/GROUP and point isolation, source permissions, and
duplicate restoration. Run the complete common and JVM suites after the
focused checks pass.

Finally commit the implementation and repeat the four project experiments
from `task.md`. Use the existing fixed baseline; do not rerun it. Preserve
the selected memory, field-limit, timeout and profiling configuration.
Compare reports and workload. Record retained/replayed contributor counts
when available. Identify the latest reached, completed and accepted run.

Pre-correction: the native example completes **run-3** without its finding.
The last OWASP campaign completes and accepts **run-5**, with 18 missing
baseline identities. These results do not establish post-fix acceptance.

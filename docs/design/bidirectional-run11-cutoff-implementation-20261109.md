# Run-11 cutoff implementation

Selected specification: [run-11 cutoff](../../spec/bidirectional-run11-cutoff.md).
The default applies to both production JVM entrypoints, including rule tests.
Only the latest completed forward witnesses supply provisional findings.

This changes execution policy and report content. It does not change transfer,
demand admission, summary restriction, Target equality or the field schedule.

## Complete barrier and cutoff

Use the existing iteration policy and barrier. The policy wrapper delegates
the field schedule and timeout. Its default last forward run is 11.

```kotlin
class HardRunLimitPolicy(delegate: IterationPolicy, lastForwardRun: Int = 11) {
    // Delegate fieldLimitSchedule, fieldLimit and timeout.
    fun continueAfter(run, result, frontiers) =
        run.index < lastForwardRun && delegate.continueAfter(run, result, frontiers)
    fun stopReason(run) =
        if (run.index >= lastForwardRun) RUN_LIMIT else delegate.stopReason(run)
}

// Existing joined barrier, with unchanged preparation and commit order:
prepared = report.prepare(config, result, shared)
persistAcceptedRecords()
handoff = prepareHandoff()
next = when {
    forward && handoff.isEmpty() -> end(NO_DEMAND_EDGE)
    forward && !policy.continueAfter(...) -> end(policy.stopReason(config))
    else -> nextRun()
}
checkCancellation()
report.commit(prepared)
return next
```

Run-12 is not constructed after a complete run-11 policy stop. A failed
engine or pre-commit barrier failure cannot commit its candidate snapshot.
Existing guard cleanup can fail after commit; preserve its committed normal
state and abnormal ending. Provisional entries remain hidden. Keep explicit native
finite policies for tests. The legacy iteration-limit option stays separate.

## Observe witnesses; keep propagation unchanged

```kotlin
fun onCompleteSinkWitness(core, sink, instruction, witness) {
    requireValidRuntimeWitness(witness) // Existing full-cube validation.
    if (core.forward) {
        id = catalog.internReached(existingPhysicalSinkKey(...), sink.rule, core.key)
        core.methodOwner.reachedSinkReportIds += id
    }
    emitExistingTargetArmsAndSeeds(witness) // Unchanged NORMAL/DEMAND rules.
}
```

Each method owns one reached-ID set. Nested loop blocks share this set through
their existing binding. This follows the existing sink-seed ownership pattern.
There is no global mutable per-run collector and no new Target kind.

`internReached` uses the existing physical-key index. If it sees an identity
before a NORMAL witness does, the first NORMAL `intern` promotes the descriptor
to that NORMAL rule/context. The integer ID stays stable. This keeps the old
first-NORMAL representative rule. Numeric IDs need not match a different scan.

## Snapshot and output

```kotlin
fun prepareForward(config, joinedResult): Snapshot {
    confirmed = collectExistingConfirmedRootTerminals()
    latest = joinedResult.analyzers.flatMap { it.reachedSinkReportIds }
        .associateWith { Entry(it, catalog.descriptor(it), provisional = true) }
    return Snapshot(existingNormalTargets, confirmed, latest)
}

fun build(end): Report {
    entries = confirmed.copy()
    if (end.reason == RUN_LIMIT)
        for ((id, candidate) in latest) entries.putIfAbsent(id, candidate)
    return Report(entries.values, end)
}
```

Backward barriers return the current snapshot. Forward barriers replace latest
IDs, including replacement with an empty set. Confirmed entries always win.
No provisional entry enters persisted NORMAL relations. A candidate observed
inside a callee is a reached local witness, not a proved root witness.

Carry `Entry.provisional` into a default-false `VulnerabilityWithTrace` flag.
After normal SARIF location, fingerprint and framework annotation, add
`properties.tags = existingTags + "opentaint:provisional"` and the notice
`Provisional finding. Later refinement may discard this finding.`
Keep rule ID, severity, location and fingerprints unchanged. Existing confirmed,
legacy and Go values keep the default false flag and unchanged output.

The extra flag participates in data-class equality. Report deduplication uses
the physical ReportId before conversion, so it cannot create separate confirmed
and provisional findings for one identity. No AP type receives this metadata.

## Files and validation

| File | Change and purpose |
| --- | --- |
| `bidi/driver/IterationPolicy.kt` | Add the default production policy wrapper and explicit stop reason |
| `bidi/driver/IterationDriver.kt` | Use the policy reason at the existing joined barrier |
| `bidi/driver/Report.kt` | Keep an immutable latest witness snapshot; select provisional entries only at RUN_LIMIT |
| `bidi/engine/BlockRunState.kt` | Own/share the reached physical IDs |
| `bidi/engine/BlockRuntimeBinding.kt` | Expose the existing method owner's observation set to child blocks |
| `bidi/engine/MethodBlockRuntime.kt` | Pass the same owner set through loop decomposition |
| `bidi/engine/RunMethodLocalServices.kt` | Observe only actual complete forward sink witnesses |
| `bidi/engine/ReportCatalog.kt` | Intern reached identities and preserve the first NORMAL representative |
| `jvm/bidi/JIRBidiAnalysis.kt` | Forward confidence to output and log confirmed/provisional counts |
| `ap/ifds/trace/VulnerabilityWithTrace.kt` | Add default-false report metadata |
| `common/sast/sarif/SarifGenerator.kt` | Add the visible and machine-readable provisional marker |

All runtime changes implement the selected bidirectional behavior. Shared DTO
and SARIF changes preserve main/Go behavior through default values. Tests cover
both schedules, early convergence, failed final barriers, latest replacement,
ND completion, nested ownership, anonymous Target deduplication, descriptor
promotion, confidence priority and serialized SARIF tags/fingerprints.

The constructive [proof package](../../spec/lean/proposals/run11-cutoff-20261109/README.md)
has twelve cap laws and ten report-selection/snapshot laws. Source correspondence
and native tests connect the finite models to the actual owner/barrier APIs.
They do not certify that a provisional finding has a concrete path.

Run full common-core tests, JVM adapter tests, focused output/legacy-option
tests, and native bidirectional project tests. Preserve existing failures and
compare them separately. Commit the implementation before fresh source-only
Java/Go rule validation. Keep the old unbounded campaign and its timeout,
controlled stop and missing final JSON explicit. In the new report, show
confirmed and provisional counts, strict rule gate results, each latest run
and RUN_LIMIT versus convergence. Repeat fixed-config project measurements
on the new runtime; do not use the old iteration counts as current results.

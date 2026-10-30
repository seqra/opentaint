package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.Record

/** Read the previous-run store on every original offer, without live input history. */
internal fun replayPersistedSummaries(
    config: RunConfig,
    ops: ApOps,
    part: Subscription,
    applier: SummaryApplier,
    statistics: N2Statistics? = null,
) {
    check(config.restricted && !part.zeroOnly)
    val records = config.records
    val direction = config.direction
    val mode = config.mode
    val cancellation = ops.manager.cancellation
    statistics?.persistedReplayStarted()
    val seen = HashSet<Record>()
    val seenViews = HashMap<RecordLeafView, Boolean>()
    for (leaf in ops.leaves(part.added)) {
        cancellation.checkpoint()
        for (record in records.byEntry(part.callee, leaf)) {
            cancellation.checkpoint()
            statistics?.persistedReplayCandidate()
            if (record.direction != direction || !seen.add(record)) continue
            val added = ops.satisfying(part.added, record.premise, mode, record = true) ?: continue
            statistics?.persistedReplayMatched()
            applier.applyRecord(part.copy(added = added), record)
        }
        for (record in records.byExit(part.callee, leaf)) {
            cancellation.checkpoint()
            statistics?.persistedReplayCandidate()
            if (record.direction == direction) continue
            record.forEachReversedAt(leaf) { view, nonSubsumable ->
                cancellation.checkpoint()
                val previous = seenViews[view]
                if (previous == true || previous == false && !nonSubsumable) return@forEachReversedAt
                seenViews[view] = previous == true || nonSubsumable
                val added = ops.satisfying(part.added, view.premise, mode, record = true)
                    ?: return@forEachReversedAt
                statistics?.persistedReplayMatched()
                applier.applyRecordView(part.copy(added = added), view, nonSubsumable)
            }
        }
    }
}

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
    for (packet in ops.manager.canonicalPackets(part.added))
        replayCanonicalPersistedSummaries(config, ops, part.copy(added = packet), applier, statistics)
}

private fun replayCanonicalPersistedSummaries(
    config: RunConfig, ops: ApOps, part: Subscription, applier: SummaryApplier, statistics: N2Statistics?,
) {
    val records = config.records
    val direction = config.direction
    val mode = config.mode
    val cancellation = ops.manager.cancellation
    statistics?.persistedReplayStarted()
    val seen = HashSet<Record>()
    val seenViews = HashMap<NativeReadKey, Boolean>()
    for (leaf in ops.leaves(part.added)) {
        cancellation.checkpoint()
        for (record in records.byEntry(part.callee, leaf)) {
            cancellation.checkpoint()
            statistics?.persistedReplayCandidate()
            if (record.direction != direction || !seen.add(record)) continue
            val added = ops.matchSummary(part.added, record.premise, mode, nativeRecordRead = true, role = SummaryMatchRole.SAVED_DIRECT) ?: continue
            statistics?.persistedReplayMatched()
            applier.applyRecord(part.copy(added = added), record)
        }
        for (record in records.byExit(part.callee, leaf)) {
            cancellation.checkpoint()
            statistics?.persistedReplayCandidate()
            if (record.direction == direction) continue
            record.forEachNativeReversedAt(leaf) { read, nonSubsumable ->
                cancellation.checkpoint()
                val key = read.semanticKey()
                val previous = seenViews[key]
                if (previous == true || previous == false && !nonSubsumable) return@forEachNativeReversedAt
                seenViews[key] = previous == true || nonSubsumable
                val packets = matchOppositeRecordPackets(ops, part.added, read, mode)
                if (packets.isEmpty()) return@forEachNativeReversedAt
                statistics?.persistedReplayMatched()
                for (added in packets)
                    applier.applyRecordView(part.copy(added = added), read.view, nonSubsumable)
            }
        }
    }
}

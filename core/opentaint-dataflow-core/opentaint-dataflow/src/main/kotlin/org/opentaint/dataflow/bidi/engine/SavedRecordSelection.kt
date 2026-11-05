package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.*

/** Both real replay and pure observations use the same selection reader; these are whole-reader totals. */
internal class SavedRecordSelectionStatistics {
    var queries = 0L
    var fallbackQueries = 0L
    var submittedLeaves = 0L
    var entryCandidates = 0L
    var outputPositions = 0L
    var selectedRecords = 0L
    var reversedViews = 0L
    var replayDirectMatches = 0L
    fun diagnosticStatistics(): String =
        "savedSelectionQueries=$queries savedSelectionFallbacks=$fallbackQueries savedSubmittedLeaves=$submittedLeaves " +
        "savedEntryCandidates=$entryCandidates savedOutputPositions=$outputPositions savedSelectedRecords=$selectedRecords " +
        "savedReversedViews=$reversedViews savedReplayDirectMatches=$replayDirectMatches"
}

/** Invocation-local positional capability. It does not participate in native record identity. */
internal class SavedRecordSelection(
    val record: Record,
    private val reversePositions: List<Pair<Pattern, List<RecordOutputPosition>>>? = null,
    private val statistics: SavedRecordSelectionStatistics? = null,
) {
    fun forEachNativeReversedAt(actual: Facts, ops: ApOps, emit: (NativeReverseRead, Boolean) -> Unit) {
        val seen = LinkedHashSet<Pair<NativeReadKey, Boolean>>()
        fun offer(view: NativeReverseRead, protected: Boolean) {
            if (seen.add(view.semanticKey() to protected)) {
                statistics?.let { it.reversedViews++ }
                emit(view, protected)
            }
        }
        val selected = reversePositions
        if (selected == null) {
            for (leaf in ops.leaves(actual)) record.forEachNativeReversedAt(leaf, ::offer)
        } else {
            for ((leaf, positions) in selected) for (position in positions) {
                ops.manager.cancellation.checkpoint()
                position.forEachNativeReversedAt(leaf, ::offer)
            }
        }
    }

    fun forEachReversedAt(actual: Facts, ops: ApOps, emit: (RecordLeafView, Boolean) -> Unit) =
        forEachNativeReversedAt(actual, ops) { read, protected -> emit(read.view, protected) }

}

/** Preserve record-first discovery, then submitted-leaf and native output-position order.
 * Unknown read views use the complete old reader; no partial positional result is committed. */
internal fun selectSavedRecords(records: RecordStore, method: MethodKey, scope: BlockScope,
                                actual: Facts, ops: ApOps, direction: Direction,
                                statistics: SavedRecordSelectionStatistics? = null): List<SavedRecordSelection> {
    statistics?.let { it.queries++ }
    val leaves = ops.leaves(actual).toList()
    statistics?.let { it.submittedLeaves += leaves.size }
    val positions = leaves.map { leaf -> records.byExitPositions(method, scope, leaf) }
    if (positions.any { it == null }) {
        statistics?.let { it.fallbackQueries++ }
        val seen = LinkedHashSet<Record>()
        for (leaf in leaves) {
            ops.manager.cancellation.checkpoint()
            for (record in records.byEntry(method, scope, leaf)) {
                statistics?.let { it.entryCandidates++ }
                if (record.direction == direction) seen += record
            }
            for (record in records.byExit(method, scope, leaf)) if (record.direction != direction) seen += record
        }
        statistics?.let { it.selectedRecords += seen.size }
        return seen.map { SavedRecordSelection(it, statistics = statistics) }
    }
    val ordered = LinkedHashSet<Record>()
    val reverse = LinkedHashMap<Record, MutableList<Pair<Pattern, List<RecordOutputPosition>>>>()
    for ((index, leaf) in leaves.withIndex()) {
        ops.manager.cancellation.checkpoint()
        for (record in records.byEntry(method, scope, leaf)) {
            statistics?.let { it.entryCandidates++ }
            if (record.direction == direction) ordered += record
        }
        val groups = LinkedHashMap<Record, MutableList<RecordOutputPosition>>()
        for (position in checkNotNull(positions[index])) {
            statistics?.let { it.outputPositions++ }
            val record = position.record
            if (record.direction == direction) continue
            ordered += record
            groups.getOrPut(record) { ArrayList() }.add(position)
        }
        for ((record, selected) in groups) reverse.getOrPut(record) { ArrayList() }
            .add(leaf to selected.sortedBy { it.ordinal })
    }
    statistics?.let { it.selectedRecords += ordered.size }
    return ordered.map { SavedRecordSelection(it, reverse[it], statistics) }
}

package org.opentaint.dataflow.bidi.driver

import org.opentaint.dataflow.bidi.ap.Direction
import org.opentaint.dataflow.bidi.ap.MarkMode
import org.opentaint.dataflow.bidi.engine.*
import java.util.Collections

enum class EndReason { STOP_RULE, NO_DEMAND_EDGE, POLICY, ABNORMAL }

data class AnalysisEnd(
    val status: RunStatus, val run: Int, val direction: Direction, val reason: EndReason,
    val run1MarkMode: MarkMode = MarkMode.FULL,
)

/** Only settled configured-root ZERO terminal identities enter the report. */
class Report(entries: List<Entry>, val end: AnalysisEnd) {
    val entries: List<Entry> = Collections.unmodifiableList(ArrayList(entries))
    data class Entry(val id: ReportId, val descriptor: ReportDescriptor)
}

/** One completed driver barrier commits retained relations and root reports together. */
class ReportBuilder {
    class Snapshot internal constructor(val normal: NormalTargetView, entries: Map<ReportId, Report.Entry>) {
        internal val entries = Collections.unmodifiableMap(LinkedHashMap(entries))
    }
    private var state = Snapshot(NormalTargetView.EMPTY, emptyMap())
    val normalTargets: NormalTargetView get() = state.normal
    val reportCount: Int get() = state.entries.size

    fun prepare(config: RunConfig, result: RunResult<RunMethodAnalyzer>, shared: SharedObjects): Snapshot {
        check(result.status == RunStatus.COMPLETE)
        if (config.direction != Direction.FORWARD) return state
        val entries = LinkedHashMap(state.entries)
        for (actor in result.analyzers) {
            shared.cancellation.checkpoint()
            if (actor.key !in config.roots) continue
            for (row in actor.targets) {
                val target = row.target as? Target.NormalTarget ?: continue
                if (row.premise.isZero) entries.putIfAbsent(target.id,
                    Report.Entry(target.id, shared.reportCatalog.descriptor(target.id)))
            }
        }
        val fresh = result.analyzers.asSequence().flatMap { actor ->
            actor.targets.asSequence().mapNotNull { row ->
                (row.target as? Target.NormalTarget)?.let { OwnedNormalTarget(actor.key, row.premise, it.id) }
            }
        }
        val normal = NormalTargetStore(shared.ap, state.normal.rows() + fresh)
        check(normal.zeroRows().all { it.id in entries }) {
            "Every retained ZERO terminal must reach a configured root before the barrier"
        }
        return Snapshot(normal, entries)
    }

    fun commit(prepared: Snapshot) { state = prepared }
    fun build(end: AnalysisEnd): Report = Report(state.entries.values.toList(), end)
}

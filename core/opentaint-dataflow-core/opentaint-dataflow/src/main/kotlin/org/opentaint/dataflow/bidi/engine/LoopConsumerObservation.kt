package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.Record
import org.opentaint.dataflow.graph.PortId

/** The router identifies the enclosing region's exit, preserving the saved row's actual port. */
internal data class LoopObservedRecord(val record: Record, val enclosingExit: PortId)
internal data class LoopObservedTarget(val row: TargetSummary, val member: Int, val enclosingExit: PortId)

/** Scope, complete original and exit are part of the observation, not only AP geometry. */
internal sealed interface LoopEnclosingResult {
    data class Data(val scope: BlockScope, val exit: PortId, val original: PremiseKey,
                    val member: LoopObservedMember) : LoopEnclosingResult
    data class Terminal(val scope: BlockScope, val exit: PortId, val original: PremiseKey,
                        val target: Target) : LoopEnclosingResult
}

/** Frozen-snapshot adapters. They perform lookups only and never publish their query results. */
internal class LoopConsumerViews(
    val enclosingScope: BlockScope,
    val enclosingIsRoot: Boolean,
    val adjacentInitials: (Facts) -> Set<AdmittedInitial>,
    val repeatInitials: (Facts) -> Set<AdmittedInitial>,
    val savedRecords: (Facts) -> Sequence<LoopObservedRecord>,
    val savedTargets: (PremiseKey, Facts) -> Sequence<LoopObservedTarget>,
    val intersectEnclosing: (PortId, PremiseKey, Facts) -> List<Facts>,
    val acceptsEnclosingTarget: (PortId, PremiseKey) -> Boolean,
    val hasSavedEnclosingTarget: (PremiseKey, ReportId) -> Boolean,
    val isPublicSummaryBase: (AccessPathBase) -> Boolean,
    val labelledAdmissions: (Facts) -> Collection<LoopLabelledAdmission> = { emptyList() },
)

/** Complete three-family observer. All scratch is local to one query invocation. */
internal class LoopConsumerObservation(
    private val ops: ApOps,
    private val mode: ApMode,
    private val views: LoopConsumerViews,
) {
    private val application = LocalRelationApplication(ops, mode)

    fun observe(original: PremiseKey, value: Facts): LoopObservation<LoopEnclosingResult> {
        val ap = ops.manager
        ap.cancellation.checkpoint()
        val adjacent = views.adjacentInitials(value)
        val full = EnclosingResults(ops)
        fun sink(exit: PortId): LocalRelationOut = object : LocalRelationOut {
            override fun data(original: PremiseKey, value: Facts) {
                ap.cancellation.checkpoint()
                if (views.enclosingIsRoot && !views.isPublicSummaryBase(value.base)) return
                val normalized = normalizeFlowSummary(ap, original, value)
                for (kept in views.intersectEnclosing(exit, normalized.premise, normalized.facts))
                    full.addData(views.enclosingScope, exit, normalized.premise, kept)
            }

            override fun target(original: PremiseKey, target: Target) {
                ap.cancellation.checkpoint()
                val accepted = when (target) {
                    Target.DemandTarget -> views.acceptsEnclosingTarget(exit, original)
                    is Target.NormalTarget -> mode.direction == Direction.FORWARD &&
                        !views.hasSavedEnclosingTarget(original, target.id)
                }
                if (accepted) full.addTarget(views.enclosingScope, exit, original, target)
            }

            // The observation is a pure query. Actual saved replay delivers its ordinary requests.
            override fun markRequest(mark: TaintMark) = Unit
        }

        val seen = LinkedHashSet<LoopObservedRecord>()
        for (saved in views.savedRecords(value)) {
            ap.cancellation.checkpoint()
            if (!seen.add(saved)) continue
            val record = saved.record
            val output = sink(saved.enclosingExit)
            if (record.direction == mode.direction) application.applyRecord(value, original, record, output)
            else {
                val reversed = LinkedHashSet<Pair<RecordLeafView, Boolean>>()
                for (leaf in ops.leaves(value)) record.forEachReversedAt(leaf) { view, protected ->
                    if (reversed.add(view to protected))
                        application.applyRecordView(value, original, view, protected, output)
                }
            }
        }
        for (saved in views.savedTargets(original, value)) {
            ap.cancellation.checkpoint()
            // A saved ZERO -> NormalTarget has no new effect. Other ND rows use a metadata
            // arm view here only; executable local replay still joins their complete binding.
            if (saved.row.premise.isZero && saved.row.target is Target.NormalTarget) continue
            val initial = saved.row.premise.member(saved.member)
            val layer = application.targetArmLayer(value, initial, saved.row.target, saved = true) ?: continue
            if (saved.row.target is Target.NormalTarget && layer != Layer.NORMAL) continue
            sink(saved.enclosingExit).target(original, saved.row.target)
        }
        val repeat = views.repeatInitials(value)
        return LoopObservation(adjacent, full.freeze(), repeat, views.labelledAdmissions(value))
    }
}

/** Union protection before freezing the complete result signature. */
private class EnclosingResults(private val ops: ApOps) {
    private data class Header(val scope: BlockScope, val exit: PortId, val original: PremiseKey)
    private val data = LinkedHashMap<Header, LoopObservedFacts>()
    private val targets = LinkedHashSet<LoopEnclosingResult.Terminal>()

    fun addData(scope: BlockScope, exit: PortId, original: PremiseKey, value: Facts) {
        data.getOrPut(Header(scope, exit, original)) { LoopObservedFacts(ops) }.add(value)
    }

    fun addTarget(scope: BlockScope, exit: PortId, original: PremiseKey, target: Target) {
        targets += LoopEnclosingResult.Terminal(scope, exit, original, target)
    }

    fun freeze(): Set<LoopEnclosingResult> = buildSet {
        for ((header, values) in data) for (member in values.freeze()) {
            ops.manager.cancellation.checkpoint()
            add(LoopEnclosingResult.Data(header.scope, header.exit, header.original, member))
        }
        addAll(targets)
    }
}

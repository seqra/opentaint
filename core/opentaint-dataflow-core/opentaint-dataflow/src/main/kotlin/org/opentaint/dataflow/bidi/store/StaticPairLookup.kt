package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*

/** C5 retains the correlated source and target for every labelled path. */
internal class StaticPairLookup(private val ap: ApManager, private val completion: FrozenCompletion,
                                private val stats: DemandQueryStatistics?,
                                private val canStoreInitial: (Pattern, InitialAp) -> Boolean) {
    fun walk(method: MethodKey, original: PremiseKey, outputs: List<Pattern>, visible: Boolean,
             offer: (InitialAp, DemandPattern) -> Unit, covered: () -> Boolean) {
        if (visible) stats?.add(11)
        val view = if (visible) completion.visible(method) else completion.local(method)
        original.forEachMember { member ->
            val targetLabels = outputCovering(member.toPattern(), ap.marks)
            val fullOriginal = (targetLabels as? StaticLabelSelection.OutputCovers)?.actual is StaticMarkSelector.Full
            val targetQuery = StaticRowQuery(targetLabels) { right -> mappedRightMayEmit(member, right, fullOriginal) }
            val keepTarget = StaticCandidateFilter { _, to, marks -> mayKeep(member, to, marks) }
            if (!view.selectedHasComposedEndpoints(member, outputs, targetQuery, keepTarget)) return@forEachMember
            val pending = ArrayDeque<StaticGuidanceEdge>()
            val seen = HashSet<StaticGuidanceEdge>()
            fun admit(edge: StaticGuidanceEdge) {
                ap.cancellation.checkpoint()
                if (!mayKeep(member, edge.to, edge.marks)) return
                if (seen.add(edge)) { stats?.add(8); pending.addLast(edge) } else stats?.add(13)
            }
            for (edge in view.selectedTargets(member.toPattern(), true, targetQuery, keepTarget)) admit(edge)
            while (pending.isNotEmpty()) {
                ap.cancellation.checkpoint()
                val state = pending.removeFirst()
                stats?.add(14)
                offer(member, DemandPattern(state.to, state.from))
                if (covered()) return
                if (state.from.fact.base != STATIC) continue
                stats?.add(15)
                val keepIncoming = StaticCandidateFilter { _, _, leftMarks ->
                    val marks = composeMarks(leftMarks, state.marks)
                    marks != null && mayKeep(member, state.to, marks)
                }
                val incomingLabels = when (val marks = state.marks) {
                    GuidanceMarks.Flow -> if (mappedRightMayEmit(member, state.to, fullOriginal)) targetLabels else StaticLabelSelection.FlowOnly
                    is GuidanceMarks.Mapped -> outputComposable(marks.input, ap.marks)
                }
                for (left in view.selectedIncoming(state.from, StaticRowQuery(incomingLabels), keepIncoming)) {
                    stats?.add(16)
                    compose(left, state)?.let { stats?.add(17); admit(it) }
                }
            }
        }
    }

    /** A false result excludes mapped rows only. FLOW remains a possible repair route. */
    private fun mappedRightMayEmit(member: InitialAp, right: Pattern, fullOriginal: Boolean): Boolean {
        if (!fullOriginal || right.fact.base == AccessPathBase.Zero) return true
        val sameMark = right.copy(fact = right.fact.copy(mark = member.mark))
        return canStoreInitial(normalizeDemandFieldExclusion(sameMark), member)
    }

    private fun mayKeep(member: InitialAp, right: Pattern, marks: GuidanceMarks): Boolean = when (marks) {
        GuidanceMarks.Flow -> true // A mapped predecessor can still make its mark admissible.
        is GuidanceMarks.Mapped -> {
            val entry = if (right.fact.base == AccessPathBase.Zero) right
                else right.copy(fact = right.fact.copy(mark = MarkSlot.Concrete(checkNotNull(marks.output))))
            canStoreInitial(normalizeDemandFieldExclusion(entry), member).also { if (!it) stats?.add(12) }
        }
    }

    private fun composeMarks(left: GuidanceMarks, right: GuidanceMarks): GuidanceMarks? = when (left) {
        GuidanceMarks.Flow -> right
        is GuidanceMarks.Mapped -> when (right) {
            GuidanceMarks.Flow -> left
            is GuidanceMarks.Mapped -> if (left.output != null && right.input != null &&
                (ap.marks.coversAtom(left.output, right.input) || ap.marks.coversAtom(right.input, left.output)))
                GuidanceMarks.Mapped(left.input, right.output) else null
        }
    }

    private fun compose(left: StaticGuidanceEdge, right: StaticGuidanceEdge): StaticGuidanceEdge? {
        if (staticAnchor(ap, left.to) != staticAnchor(ap, right.from) || !overlap(left.to, right.from)) return null
        val relation = composeMarks(left.marks, right.marks) ?: return null
        fun endpoint(p: Pattern, mark: TaintMark?): Pattern = when {
            p.fact.base == AccessPathBase.Zero -> p // genuine ZERO, never a new full-mark sentinel
            relation == GuidanceMarks.Flow -> p.copy(fact = p.fact.copy(mark = MarkSlot.STAR))
            else -> p.copy(fact = p.fact.copy(mark = MarkSlot.Concrete(checkNotNull(mark))))
        }
        val mapped = relation as? GuidanceMarks.Mapped
        return StaticGuidanceEdge(endpoint(left.from, mapped?.input), endpoint(right.to, mapped?.output), relation)
    }
}

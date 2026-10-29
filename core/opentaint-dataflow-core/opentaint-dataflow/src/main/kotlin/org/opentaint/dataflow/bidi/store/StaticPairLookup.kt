package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*

/** C5 retains the correlated source and target for every labelled path. */
internal class StaticPairLookup(private val ap: ApManager, private val completion: FrozenCompletion,
                                private val stats: DemandQueryStatistics?,
                                @Suppress("unused") private val canStoreInitial: (Pattern, InitialAp) -> Boolean) {
    fun walk(method: MethodKey, original: PremiseKey, outputs: List<Pattern>, visible: Boolean,
             offer: (InitialAp, DemandPattern) -> Unit, covered: () -> Boolean) {
        if (visible) stats?.add(11)
        val view = if (visible) completion.visible(method) else completion.local(method)
        original.forEachMember { member ->
            if (!view.hasComposedEndpoints(member, outputs)) return@forEachMember
            val pending = ArrayDeque<StaticGuidanceEdge>()
            val seen = HashSet<StaticGuidanceEdge>()
            fun admit(edge: StaticGuidanceEdge) {
                ap.cancellation.checkpoint()
                if (seen.add(edge)) { stats?.add(8); pending.addLast(edge) }
            }
            for (edge in view.targets(member.toPattern(), prefixesOnly = true)) admit(edge)
            while (pending.isNotEmpty()) {
                ap.cancellation.checkpoint()
                val state = pending.removeFirst()
                offer(member, DemandPattern(state.to, state.from))
                if (covered()) return
                if (state.from.fact.base != STATIC) continue
                for (left in view.incoming(state.from)) compose(left, state)?.let(::admit)
            }
        }
    }

    private fun compose(left: StaticGuidanceEdge, right: StaticGuidanceEdge): StaticGuidanceEdge? {
        if (staticAnchor(ap, left.to) != staticAnchor(ap, right.from) || !overlap(left.to, right.from)) return null
        val relation = when (val l = left.marks) {
            GuidanceMarks.Flow -> right.marks
            is GuidanceMarks.Mapped -> when (val r = right.marks) {
                GuidanceMarks.Flow -> l
                is GuidanceMarks.Mapped -> if (l.output != null && r.input != null &&
                    (ap.marks.coversAtom(l.output, r.input) || ap.marks.coversAtom(r.input, l.output)))
                    GuidanceMarks.Mapped(l.input, r.output) else return null
            }
        }
        fun endpoint(p: Pattern, mark: TaintMark?): Pattern = when {
            p.fact.base == AccessPathBase.Zero -> p // genuine ZERO, never a new full-mark sentinel
            relation == GuidanceMarks.Flow -> p.copy(fact = p.fact.copy(mark = MarkSlot.STAR))
            else -> p.copy(fact = p.fact.copy(mark = MarkSlot.Concrete(checkNotNull(mark))))
        }
        val mapped = relation as? GuidanceMarks.Mapped
        return StaticGuidanceEdge(endpoint(left.from, mapped?.input), endpoint(right.to, mapped?.output), relation)
    }
}

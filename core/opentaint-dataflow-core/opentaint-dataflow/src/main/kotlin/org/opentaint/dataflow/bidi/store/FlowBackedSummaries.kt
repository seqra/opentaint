package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import java.util.IdentityHashMap

/** One summary endpoint owns this normalized relation. No old marked payloads are retained.
 * Raw, selected and published endpoints each use the same admission law. */
internal class FlowBackedSummaries(private val m: ApManager,
                                   private val replaceCovered: Boolean = true,
                                   private val interners: StoreInterners = m.newInterners()) {
    private val groups = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val concreteByShape = IdentityHashMap<InitialAp, MutableSet<PremiseKey>>()
    private val diagonal = DiagonalRelations(m, interners)

    /** A method-point neutral continuation admits its mask before any scalar
     * materialization. Summary boundaries keep their existing producer hooks. */
    fun addDiagonal(offered: DiagonalDelta): List<DiagonalDelta>? =
        if (replaceCovered) null else diagonal.addDiagonal(offered)

    fun census(): RelationCensus {
        m.cancellation.checkpoint()
        val counter = RelationCensusCounter(m.cancellation)
        var result = diagonal.census(counter)
        for (group in groups.values) for (facts in group.all()) {
            m.cancellation.checkpoint()
            result += counter.scalar(facts)
        }
        return result
    }

    fun add(premise: PremiseKey, offered: Facts): Facts? {
        m.cancellation.checkpoint()
        if (offered is FlowTree) {
            val delta = groups.getOrPut(premise) { ConclusionGroup(m, interners) }.add(offered) ?: return null
            val initial = premise as InitialAp
            if (!replaceCovered) return delta
            diagonal.compact(initial, delta as FlowTree)
            // Only unsupported mixed/cross-mark rows live in these groups.
            // Rebuild their current residual, not a replay or history record.
            for (key in concreteByShape[initial].orEmpty()) {
                m.cancellation.checkpoint()
                val current = groups[key] ?: continue
                val replacement = ConclusionGroup(m, interners)
                for (facts in current.all()) normalize(key, facts)?.let(replacement::add)
                groups[key] = replacement
            }
            return delta
        }
        val residual = normalize(premise, offered) ?: return null
        if (diagonal.supports(premise, residual)) return diagonal.add(premise, residual)
        // A cross-mark or exact sibling must not create a second authoritative
        // copy of the diagonal membership in the scalar fallback.
        if (residual is TaintTree && (residual.anyTail == Tail.STAR || residual.anyTail == Tail.ANY)) {
            val initial = flowInitialForCoverage(m, premise)
            val mark = ((premise as? InitialAp)?.mark as? MarkSlot.Concrete)?.mark
            if (initial != null && mark != null) {
                val mask = m.markSetOf(mark)
                val root = m.taintAlg.mapLeaves(residual.root, m.cancellation) {
                    m.taintLeaves(MarkSet.EMPTY, it.any intersect mask)
                }
                if (root != null) {
                    val part = residual.withRoot(root)
                    val fresh = diagonal.add(premise, part)
                    val rest = ApOps(m).without(residual, part)
                    val extra = rest?.let { addFallback(premise, it) }
                    return when {
                        fresh == null -> extra
                        extra == null -> fresh
                        else -> {
                            val result = m.taintTree(residual.base, residual.layer,
                                m.taintAlg.mergeAdd((fresh as TaintTree).root, (extra as TaintTree).root, m.cancellation),
                                residual.exclusion, residual.anyTail)
                            val flag = fresh.nonSubsumable?.let { a -> extra.nonSubsumable?.let {
                                m.taintAlg.mergeAdd(a, it, m.cancellation)
                            } ?: a } ?: extra.nonSubsumable
                            result.withProtection(flag)
                        }
                    }
                }
            }
        }
        return addFallback(premise, residual)
    }

    private fun addFallback(premise: PremiseKey, residual: Facts): Facts? {
        if (replaceCovered) flowInitialForCoverage(m, premise)?.let { shape ->
            concreteByShape.getOrPut(shape) { java.util.Collections.newSetFromMap(IdentityHashMap()) }.add(premise)
        }
        return groups.getOrPut(premise) { ConclusionGroup(m, interners) }.add(residual)
    }

    /** All supported typed cells use the same coverage law. Call consumers
     * retain their own identity classifier; it is not a summary-store guard. */
    fun normalize(premise: PremiseKey, facts: Facts): Facts? {
        if (!replaceCovered || facts !is TaintTree || (facts.anyTail != Tail.STAR && facts.anyTail != Tail.ANY)) return facts
        val initial = flowInitialForCoverage(m, premise) ?: return facts
        val flow = groups[initial]?.all()?.filterIsInstance<FlowTree>() ?: return facts
        return removeFlowCovered(m, premise, facts, flow.asIterable(), facts.nonSubsumable)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = sequence {
        for ((premise, group) in groups) {
            m.cancellation.checkpoint()
            for (facts in group.all()) yield(premise to facts)
        }
        yieldAll(diagonal.all())
    }

    fun borrow(premise: PremiseKey): Sequence<Facts> = sequence {
        yieldAll(groups[premise]?.all() ?: emptySequence())
        yieldAll(diagonal.borrow(premise))
    }
}

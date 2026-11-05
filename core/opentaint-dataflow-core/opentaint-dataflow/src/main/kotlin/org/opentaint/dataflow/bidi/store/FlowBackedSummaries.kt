package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import java.util.IdentityHashMap

/** One summary endpoint owns this normalized relation. No old marked payloads are retained.
 * Each endpoint keeps one authoritative relation with its existing admission law. */
internal class FlowBackedSummaries(private val m: ApManager,
                                   private val replaceCovered: Boolean = true,
                                   private val interners: StoreInterners = m.newInterners(),
                                   private val normalStars: NormalStarRelationIndex? = null,
                                   private val emptied: (PremiseKey) -> Unit = {}) {
    private val groups = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val concreteByShape = IdentityHashMap<InitialAp, MutableSet<PremiseKey>>()
    private val diagonal = DiagonalRelations(m, interners)
    private val concreteShapes = PathTrie<InitialAp>(m.cancellation)

    /** A method-point neutral continuation admits its mask before any scalar
     * materialization. Summary boundaries keep their existing producer hooks. */
    fun addDiagonal(offered: DiagonalDelta): List<DiagonalDelta>? =
        if (!RuntimeDataDomain.initial(offered.initialShape) || !RuntimeDataDomain.base(offered.base)) emptyList()
        else if (replaceCovered) null else diagonal.addDiagonal(offered)

    fun census(include: (PremiseKey, Layer) -> Boolean = { _, _ -> true }): RelationCensus {
        m.cancellation.checkpoint()
        val counter = RelationCensusCounter(m.cancellation)
        var result = diagonal.census(counter, include)
        for ((premise, group) in groups) for (facts in group.all()) {
            m.cancellation.checkpoint()
            if (include(premise, facts.layer)) result += counter.scalar(facts)
        }
        normalStars?.all()?.forEach { (premise, facts) ->
            if (include(premise, facts.layer)) result += counter.scalar(facts)
        }
        return result
    }

    fun add(premise: PremiseKey, offered: Facts): Facts? = addAll(premise, offered).also {
        check(it.size <= 1) { "Use addAll for a split canonical header" }
    }.singleOrNull()

    fun addAll(premise: PremiseKey, offered: Facts): List<Facts> {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, offered)) return emptyList()
        if (offered is FlowTree) {
            val initial = premise as InitialAp
            if (normalStars?.supports(initial, offered) == true) {
                val update = normalStars.add(initial, offered)
                if (update.affectedInitials.isNotEmpty()) {
                    // Include concrete-only shapes: there need not have been an old FLOW L.
                    for (shape in concreteShapes.lookupExtensions(initial.base, initial.pathData)) refreshConcrete(shape)
                }
                return update.fresh
            }
            val delta = groups.getOrPut(premise) { ConclusionGroup(m, interners) }.addAll(offered)
            if ((replaceCovered || normalStars != null) && delta.isNotEmpty()) refreshConcrete(initial)
            return delta
        }
        val residual = normalize(premise, offered) ?: return emptyList()
        rememberConcrete(premise)
        // The scalar summary backend gains the selected NORMAL relation law only.
        // Point owners have no normalStars and retain their existing diagonal path.
        if (!replaceCovered && normalStars != null) return addFallback(premise, residual)
        if (diagonal.supports(premise, residual)) return diagonal.addAll(premise, residual)
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
                    val fresh = diagonal.addAll(premise, part)
                    val rest = ApOps(m).without(residual, part)
                    val extra = rest?.let { addFallback(premise, it) }.orEmpty()
                    val result = ConclusionGroup(m, interners)
                    for (value in fresh + extra) result.addAll(value)
                    return result.all().toList()
                }
            }
        }
        return addFallback(premise, residual)
    }

    private fun addFallback(premise: PremiseKey, residual: Facts): List<Facts> =
        groups.getOrPut(premise) { ConclusionGroup(m, interners) }.addAll(residual)

    private fun rememberConcrete(premise: PremiseKey) {
        if (replaceCovered || normalStars != null) flowInitialForCoverage(m, premise)?.let { shape ->
            concreteByShape.getOrPut(shape) {
                concreteShapes.add(shape.base, shape.pathData, shape)
                java.util.Collections.newSetFromMap(IdentityHashMap())
            }.add(premise)
        }
    }

    private fun flowCovers(shape: InitialAp): List<FlowTree> = buildList {
        if (replaceCovered) groups[shape]?.all()?.filterIsInstance<FlowTree>()?.forEach(::add)
        normalStars?.visitSpecializedCovers(shape, ::add)
    }

    private fun refreshConcrete(shape: InitialAp) {
        val covers = flowCovers(shape)
        if (replaceCovered) for (flow in covers) diagonal.compact(shape, flow)
        val keys = concreteByShape[shape] ?: return
        for (key in keys.toList()) {
            m.cancellation.checkpoint()
            groups[key]?.let { current ->
                val replacement = ConclusionGroup(m, interners)
                for (facts in current.all()) normalize(key, facts)?.let { replacement.addAll(it) }
                if (replacement.all().none()) groups.remove(key) else groups[key] = replacement
            }
            if (groups[key]?.all()?.any() != true && diagonal.borrow(key).none()) {
                keys.remove(key)
                emptied(key)
            }
        }
        if (keys.isEmpty()) {
            concreteByShape.remove(shape)
            concreteShapes.remove(shape.base, shape.pathData, shape)
        }
    }

    /** All supported typed cells use the same coverage law. Call consumers
     * retain their own identity classifier; it is not a summary-store guard. */
    fun normalize(premise: PremiseKey, facts: Facts): Facts? {
        if (facts is FlowTree && premise is InitialAp && normalStars?.supports(premise, facts) == true)
            return normalStars.retainCurrent(premise, facts)
        if ((!replaceCovered && normalStars == null) || facts !is TaintTree ||
            (facts.anyTail != Tail.STAR && facts.anyTail != Tail.ANY)) return facts
        val initial = flowInitialForCoverage(m, premise) ?: return facts
        return removeFlowCovered(m, premise, facts, flowCovers(initial), facts.nonSubsumable)
    }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = sequence {
        for ((premise, group) in groups) {
            m.cancellation.checkpoint()
            for (facts in group.all()) yield(premise to facts)
        }
        yieldAll(diagonal.all())
        normalStars?.all()?.forEach { yield(it.first to it.second) }
    }

    fun borrow(premise: PremiseKey): Sequence<Facts> = sequence {
        yieldAll(groups[premise]?.all() ?: emptySequence())
        yieldAll(diagonal.borrow(premise))
        yieldAll(normalStars?.borrowExact(premise) ?: emptySequence())
    }

    fun retainCurrentAll(premise: PremiseKey, offered: Facts): List<Facts> =
        retainCurrentFacts(m, offered, borrow(premise).asIterable())
}

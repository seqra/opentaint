package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import java.util.IdentityHashMap

/** One summary endpoint owns this normalized relation. No old marked payloads are retained.
 * Each endpoint keeps one authoritative relation with its existing admission law. */
internal class FlowBackedSummaries(private val m: ApManager,
                                   private val replaceCovered: Boolean = true,
                                   private val interners: StoreInterners = m.newInterners(),
                                   private val onPremiseRemoved: ((PremiseKey) -> Unit)? = null) {
    private val groups = IdentityHashMap<PremiseKey, ConclusionGroup>()
    private val diagonal = DiagonalRelations(m, interners)
    private val flowIndex = PathTrie<InitialAp>(m.cancellation)
    private val concreteIndex = PathTrie<PremiseKey>(m.cancellation)
    private val indexedFlow = java.util.Collections.newSetFromMap(IdentityHashMap<InitialAp, Boolean>())
    private val indexedConcrete = java.util.Collections.newSetFromMap(IdentityHashMap<PremiseKey, Boolean>())

    private fun providers(initial: InitialAp): Sequence<Pair<InitialAp, FlowTree>> = sequence {
        for (key in flowIndex.lookupPrefixes(initial.base, initial.pathArray))
            for (flow in groups[key]?.all().orEmpty().filterIsInstance<FlowTree>()) yield(key to flow)
    }

    private fun coveringFlows(initial: InitialAp): Sequence<FlowTree> = sequence {
        for ((key, value) in providers(initial)) {
            if (key === initial) yield(value.copyWithCombinedExclusion(key))
            else specializeNormalFlow(m, key, value, initial)?.let { yield(it) }
        }
    }

    private fun FlowTree.copyWithCombinedExclusion(key: InitialAp): FlowTree =
        if (tail == Tail.STAR) m.flowTree(base, layer, exclusion.union(key.exclusion), markExclusion, root, tail)
        else this

    fun addAll(premise: PremiseKey, facts: Facts): List<Facts> =
        facts.membershipPackets(m).flatMap { addPacket(premise, it) }

    fun add(premise: PremiseKey, facts: Facts): Facts? = addAll(premise, facts).also {
        check(it.size <= 1) { "Use addAll for a multi-packet summary delta" }
    }.singleOrNull()

    private fun recompact(flowInput: InitialAp) {
        // Derived positional entries may outlive a removed row. Only groups is authoritative.
        for (key in flowIndex.lookupExtensions(flowInput.base, flowInput.pathArray)) {
            val current = groups[key]?.all()?.toList().orEmpty()
            if (current.isEmpty()) continue
            val replacement = ConclusionGroup(m, interners)
            for (facts in current) {
                val kept = if (facts is FlowTree)
                    removeAlignedFlowCovered(m, key, facts,
                        providers(key).filter { (p, f) -> p !== key || f !== facts }) else facts
                kept?.let { replacement.addAll(it) }
            }
            if (replacement.all().none()) {
                groups.remove(key)
                flowIndex.remove(key.base,key.pathArray,key)
                indexedFlow.remove(key)
                onPremiseRemoved?.invoke(key)
            } else groups[key] = replacement
        }
        for (key in concreteIndex.lookupExtensions(flowInput.base, flowInput.pathArray)) {
            val shape = flowInitialForCoverage(m, key) ?: continue
            for (flow in coveringFlows(shape)) diagonal.compact(shape, flow)
            val current = groups[key]?.all()?.toList().orEmpty()
            if (current.isNotEmpty()) {
                val replacement = ConclusionGroup(m, interners)
                for (facts in current) normalize(key, facts)?.let { replacement.addAll(it) }
                if (replacement.all().none()) groups.remove(key) else groups[key] = replacement
            }
            if (groups[key]?.all()?.any() != true && diagonal.borrow(key).none()) {
                concreteIndex.remove(shape.base,shape.pathArray,key)
                indexedConcrete.remove(key)
                onPremiseRemoved?.invoke(key)
            }
        }
    }

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
        return result
    }

    private fun addPacket(premise: PremiseKey, offered: Facts): List<Facts> {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, offered)) return emptyList()
        if (offered is FlowTree) {
            val initial = premise as InitialAp
            val retained = if (replaceCovered) removeAlignedFlowCovered(m, initial, offered, providers(initial))
                ?: return emptyList() else offered
            val delta = groups.getOrPut(premise) { ConclusionGroup(m, interners) }.addAll(retained)
            if (delta.isEmpty()) return emptyList()
            if (replaceCovered && indexedFlow.add(initial)) flowIndex.add(initial.base, initial.pathArray, initial)
            if (replaceCovered) recompact(initial)
            return delta.mapNotNull { normalize(premise,it) }
        }
        val residual = normalize(premise, offered) ?: return emptyList()
        if (replaceCovered) flowInitialForCoverage(m,premise)?.let {
            if (indexedConcrete.add(premise)) concreteIndex.add(it.base,it.pathArray,premise)
        }
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
                    return fresh + (rest?.let {
                        groups.getOrPut(premise) { ConclusionGroup(m, interners) }.addAll(it)
                    } ?: emptyList())
                }
            }
        }
        return groups.getOrPut(premise) { ConclusionGroup(m, interners) }.addAll(residual)
    }

    /** All supported typed cells use the same coverage law. Call consumers
     * retain their own identity classifier; it is not a summary-store guard. */
    fun normalize(premise: PremiseKey, facts: Facts): Facts? {
        if (!replaceCovered) return facts
        if (facts is FlowTree && premise is InitialAp) {
            return removeAlignedFlowCovered(m, premise, facts, providers(premise).filter { (key, value) ->
                key !== premise || value.groupKey != facts.groupKey
            })
        }
        if (facts !is TaintTree || (facts.anyTail != Tail.STAR && facts.anyTail != Tail.ANY)) return facts
        val initial = flowInitialForCoverage(m, premise) ?: return facts
        val flow = coveringFlows(initial)
        return removeFlowCovered(m, premise, facts, flow.asIterable(), facts.nonSubsumable)
    }

    /** Exact membership intersection with the final basis, after normalization.
     * Semantic coverage by a parent is not an additional retained child. */
    fun retainedPart(premise: PremiseKey, offered: Facts): Facts? =
        normalize(premise,offered)?.let { finalMembershipPart(m,it,borrow(premise)) }

    fun all(): Sequence<Pair<PremiseKey, Facts>> = sequence {
        m.cancellation.checkpoint()
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

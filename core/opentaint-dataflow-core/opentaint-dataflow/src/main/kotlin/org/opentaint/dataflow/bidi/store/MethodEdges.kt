package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet
import java.util.IdentityHashMap

/** One writer owns completed post-statement results for a run. A row at S is
 * the output of S, never its incoming input or the output of a predecessor. */
class MethodEdgeStore(private val m: ApManager, private val method: MethodKey, private val lm: LanguageManager,
                      private val fieldLimit: Int, flowBacked: Boolean = false) {
    init { require(fieldLimit >= 1) { "The field limit must be positive" } }

    private val size = lm.getMaxInstIndex(method.method) + 1
    private val reach = IdentityHashMap<PremiseKey, Array<BitSet>>()
    private val groups = IdentityHashMap<PremiseKey, Array<ConclusionGroup?>>()
    private val interners = m.newInterners()
    // Local rule observations still need concrete membership. Share its exact
    // diagonal geometry here; semantic replacement is a summary boundary only.
    private val packed: Array<FlowBackedSummaries?>? = if (flowBacked) arrayOfNulls(size) else null

    /** Null selects the exact scalar fallback; an empty result is a duplicate.
     * The packet decoder, not its FLOW-shaped storage key, determines K6. */
    fun addDiagonal(node: CommonInst, offered: DiagonalDelta): List<DiagonalDelta>? {
        m.cancellation.checkpoint()
        val statements = packed ?: return null
        check(offered.initialShape.manager === m) { "A diagonal packet needs an owned initial shape" }
        check(offered.base !is AccessPathBase.CleanerTemporary && offered.base != AccessPathBase.Zero)
        assert(offered.geometry.boundedDepth <= fieldLimit) { "W3: a stored conclusion must be within the field limit" }
        val index = lm.getInstIndex(node)
        val owner = statements[index] ?: FlowBackedSummaries(m, replaceCovered = false, interners = interners)
            .also { statements[index] = it }
        return owner.addDiagonal(offered)
    }

    /** T4: new leaves, or the whole merged value when a T2 annotation changes. */
    fun add(node: CommonInst, premise: PremiseKey, f: Facts): Facts? {
        m.cancellation.checkpoint()
        check(f.base !is AccessPathBase.CleanerTemporary) { "A field-action temporary cannot enter method storage" }
        check((f is FlowTree) == premise.isFlow) { "K6: the conclusion kind follows the premise" }
        check(premise !is PremiseSet || f is TaintTree) { "A multi-premise edge must be TAINT" }
        val index = lm.getInstIndex(node)
        when (f) {
            is Reach -> {
                val bits = reach.getOrPut(premise) { arrayOf(BitSet(size), BitSet(size)) }[f.layer.ordinal]
                if (bits[index]) return null
                bits.set(index)
                return f
            }
            is FlowTree -> assert(f.root.boundedDepth <= fieldLimit) { "W3: a stored conclusion must be within the field limit" }
            is TaintTree -> assert(f.root.boundedDepth <= fieldLimit) { "W3: a stored conclusion must be within the field limit" }
        }
        packed?.let { statements ->
            val owner = statements[index] ?: FlowBackedSummaries(m, replaceCovered = false, interners = interners)
                .also { statements[index] = it }
            return owner.add(premise, f)
        }
        val statements = groups.getOrPut(premise) { arrayOfNulls(size) }
        val group = statements[index] ?: ConclusionGroup(m, interners).also { statements[index] = it }
        return group.add(f)
    }

    /** Test view of all complete stored values at a statement. */
    fun edgesAt(node: CommonInst, premise: PremiseKey? = null): Sequence<Pair<PremiseKey, Facts>> = sequence {
        m.cancellation.checkpoint()
        val index = lm.getInstIndex(node)
        packed?.get(index)?.let { owner ->
            if (premise == null) yieldAll(owner.all())
            else for (facts in owner.borrow(premise)) yield(premise to facts)
        }
        val keys = if (premise != null) listOf(premise) else LinkedHashSet<PremiseKey>().also { keys ->
            for (key in reach.keys) { m.cancellation.checkpoint(); keys += key }
            for (key in groups.keys) { m.cancellation.checkpoint(); keys += key }
        }
        for (key in keys) {
            m.cancellation.checkpoint()
            val bits = reach[key]
            for (layer in Layer.entries) if (bits != null && bits[layer.ordinal][index]) {
                m.cancellation.checkpoint()
                yield(key to Reach.of(layer))
            }
            val group = groups[key]?.get(index) ?: continue
            for (value in group.all()) {
                m.cancellation.checkpoint()
                yield(key to value)
            }
        }
    }

    /** Full leaf matching returns the whole stored value, including its off-query leaves. */
    fun edgesAt(node: CommonInst, pattern: Pattern): Sequence<Pair<PremiseKey, Facts>> = sequence {
        m.cancellation.checkpoint()
        val path = pattern.fact.path.toIntArray()
        val ops = ApOps(m)
        for ((premise, facts) in edgesAt(node)) {
            m.cancellation.checkpoint()
            if (facts.base == pattern.fact.base && ops.leavesNear(facts, path).any {
                m.cancellation.checkpoint()
                overlap(it, pattern)
            }) yield(premise to facts)
        }
    }
}

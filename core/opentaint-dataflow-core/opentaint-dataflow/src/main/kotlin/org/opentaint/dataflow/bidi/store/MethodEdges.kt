package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.BitSet
import java.util.IdentityHashMap

/** A dense directory belongs to one block. Equal AP facts in different
 * directories do not share a post-statement admission cell. */
interface PointDirectory<P> {
    val size: Int
    fun index(point: P): Int
}

/** One writer owns completed post-point results for a run. A row at S is
 * the output of S, never its incoming input or the output of a predecessor. */
open class ScopedEdgeStore<P>(private val m: ApManager, private val points: PointDirectory<P>,
                             private val fieldLimit: Int, flowBacked: Boolean = false,
                             collectStatistics: Boolean = false) {
    init {
        require(fieldLimit >= 1) { "The field limit must be positive" }
        require(points.size >= 0) { "A point directory cannot have negative size" }
    }

    private val size = points.size
    private fun pointIndex(point: P): Int = points.index(point).also {
        require(it in 0 until size) { "A point must belong to this block directory: $it of $size" }
    }
    private val reach = IdentityHashMap<PremiseKey, Array<BitSet>>()
    private val groups = IdentityHashMap<PremiseKey, ScalarPremiseRows>()
    private val statistics = if (collectStatistics) ScalarCounters() else null

    /** A premise owns its point bits. Only competing images allocate full cells. */
    private class ScalarPremiseRows(val initial: InitialAp?) {
        var normal: BitSet? = null
        var demand: BitSet? = null
        var protectedNormal: BitSet? = null
        var protectedDemand: BitSet? = null
        var full: Array<ConclusionGroup?>? = null

        private fun bits(layer: Layer, protection: Boolean, allocate: Boolean): BitSet? {
            val old = when (layer) {
                Layer.NORMAL -> if (protection) protectedNormal else normal
                Layer.DEMAND -> if (protection) protectedDemand else demand
            }
            if (old != null || !allocate) return old
            val fresh = BitSet()
            when (layer) {
                Layer.NORMAL -> if (protection) protectedNormal = fresh else normal = fresh
                Layer.DEMAND -> if (protection) protectedDemand = fresh else demand = fresh
            }
            return fresh
        }

        fun present(layer: Layer, index: Int, protection: Boolean = false) = bits(layer, protection, false)?.get(index) == true
        fun isProtected(layer: Layer, index: Int) = bits(layer, true, false)?.get(index) == true
        fun setPresent(layer: Layer, index: Int, protection: Boolean = false) { bits(layer, protection, true)!!.set(index) }
        fun setProtected(layer: Layer, index: Int) { bits(layer, true, true)!!.set(index) }
        fun ensureFull(size: Int): Array<ConclusionGroup?> =
            full ?: arrayOfNulls<ConclusionGroup>(size).also { full = it }
        fun clearIdentityBitsAt(index: Int) {
            normal?.clear(index); demand?.clear(index)
            protectedNormal?.clear(index); protectedDemand?.clear(index)
        }
    }

    private class ScalarCounters {
        var promotedPoints = 0L
        var firstFullPoints = 0L
        val fallbackReasons = HashMap<String, Long>()
    }
    private val interners = m.newInterners()
    // Local rule observations still need concrete membership. Share its exact
    // diagonal geometry here; semantic replacement is a summary boundary only.
    private val packed: Array<FlowBackedSummaries?>? = if (flowBacked) arrayOfNulls(size) else null

    /** Null selects the exact scalar fallback; an empty result is a duplicate.
     * The packet decoder, not its FLOW-shaped storage key, determines K6. */
    fun addDiagonal(node: P, offered: DiagonalDelta): List<DiagonalDelta>? {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.initial(offered.initialShape) || !RuntimeDataDomain.base(offered.base)) return emptyList()
        val statements = packed ?: return null
        check(offered.initialShape.manager === m) { "A diagonal packet needs an owned initial shape" }
        check(offered.base !is AccessPathBase.CleanerTemporary && offered.base != AccessPathBase.Zero)
        assert(offered.geometry.boundedDepth <= fieldLimit) { "W3: a stored conclusion must be within the field limit" }
        val index = pointIndex(node)
        val owner = statements[index] ?: FlowBackedSummaries(m, replaceCovered = false, interners = interners)
            .also { statements[index] = it }
        return owner.addDiagonal(offered)
    }

    /** T4: new leaves, or the whole merged value when a T2 annotation changes. */
    fun add(node: P, premise: PremiseKey, f: Facts): Facts? = addAll(node, premise, f).let {
        check(it.size <= 1) { "Canonical point admission produced multiple packets; use addAll" }
        it.singleOrNull()
    }

    fun addAll(node: P, premise: PremiseKey, f: Facts): List<Facts> =
        f.membershipPackets(m).flatMap { addPacket(node, premise, it) }

    private fun addPacket(node: P, premise: PremiseKey, f: Facts): List<Facts> {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(premise, f)) return emptyList()
        check(f.base !is AccessPathBase.CleanerTemporary) { "A field-action temporary cannot enter method storage" }
        check((f is FlowTree) == premise.isFlow) { "K6: the conclusion kind follows the premise" }
        check(premise !is PremiseSet || f is TaintTree) { "A multi-premise edge must be TAINT" }
        val index = pointIndex(node)
        when (f) {
            is Reach -> {
                val bits = reach.getOrPut(premise) { arrayOf(BitSet(size), BitSet(size)) }[f.layer.ordinal]
                if (bits[index]) return emptyList()
                bits.set(index)
                return listOf(f)
            }
            is FlowTree -> assert(f.root.boundedDepth <= fieldLimit) { "W3: a stored conclusion must be within the field limit" }
            is TaintTree -> assert(f.root.boundedDepth <= fieldLimit) { "W3: a stored conclusion must be within the field limit" }
        }
        packed?.let { statements ->
            val owner = statements[index] ?: FlowBackedSummaries(m, replaceCovered = false, interners = interners)
                .also { statements[index] = it }
            return owner.addAll(premise, f)
        }
        val rows = groups.getOrPut(premise) {
            ScalarPremiseRows((premise as? InitialAp)?.takeUnless { it.isZero })
        }
        rows.full?.get(index)?.let { return it.addAll(f) }
        val kind = rows.initial?.let { m.identityKind(it, f) } ?: NOT_IDENTITY
        if (kind == NOT_IDENTITY) return promoteAndAdd(rows, index, f)
        val protected = kind == PROTECTED_IDENTITY
        if (rows.present(f.layer, index, protected)) return emptyList()
        rows.setPresent(f.layer, index, protected)
        return listOf(f)
    }

    /** Restore current compact images only. The restoration delta never escapes. */
    private fun promoteAndAdd(rows: ScalarPremiseRows, index: Int, offered: Facts): List<Facts> {
        val group = ConclusionGroup(m, interners)
        var promoted = false
        for (layer in Layer.entries) {
            m.cancellation.checkpoint()
            for (protected in listOf(false, true)) if (rows.present(layer, index, protected)) {
                promoted = true
                group.add(initialImage(m, checkNotNull(rows.initial), layer, protected))
            }
        }
        m.cancellation.checkpoint()
        rows.ensureFull(size)[index] = group
        rows.clearIdentityBitsAt(index)
        statistics?.let {
            if (promoted) it.promotedPoints++ else it.firstFullPoints++
            val reason = literalImageFallbackReason(rows.initial, offered)
            it.fallbackReasons[reason] = (it.fallbackReasons[reason] ?: 0L) + 1L
        }
        return group.addAll(offered)
    }

    /** Scan only on an explicit enabled request, at a quiescent owner boundary.
     * The returned object contains scalars only and cannot retain the actor. */
    fun scalarStatisticsSnapshot(): ScalarIdentityStatistics? {
        val counters = statistics ?: return null
        var compactPoints = 0L
        var compactNormal = 0L
        var compactDemand = 0L
        var compactFlow = 0L
        var compactTaint = 0L
        var protectedNormal = 0L
        var protectedDemand = 0L
        var fullPoints = 0L
        var bitWords = 0L
        var fullArrayCapacity = 0L
        for (rows in groups.values) {
            m.cancellation.checkpoint()
            val plainNormal = rows.normal?.cardinality()?.toLong() ?: 0L
            val plainDemand = rows.demand?.cardinality()?.toLong() ?: 0L
            val flaggedNormal = rows.protectedNormal?.cardinality()?.toLong() ?: 0L
            val flaggedDemand = rows.protectedDemand?.cardinality()?.toLong() ?: 0L
            val normal = plainNormal + flaggedNormal
            val demand = plainDemand + flaggedDemand
            compactNormal += normal
            compactDemand += demand
            val occupied = BitSet()
            for (bits in listOfNotNull(rows.normal, rows.demand, rows.protectedNormal, rows.protectedDemand))
                occupied.or(bits)
            compactPoints += occupied.cardinality().toLong()
            if (rows.initial?.isFlow == true) compactFlow += normal + demand else compactTaint += normal + demand
            protectedNormal += rows.protectedNormal?.cardinality()?.toLong() ?: 0L
            protectedDemand += rows.protectedDemand?.cardinality()?.toLong() ?: 0L
            bitWords += (rows.normal?.size()?.toLong() ?: 0L) / 64L
            bitWords += (rows.demand?.size()?.toLong() ?: 0L) / 64L
            bitWords += (rows.protectedNormal?.size()?.toLong() ?: 0L) / 64L
            bitWords += (rows.protectedDemand?.size()?.toLong() ?: 0L) / 64L
            rows.full?.let { cells ->
                fullArrayCapacity += cells.size
                for (cell in cells) {
                    m.cancellation.checkpoint()
                    if (cell != null) fullPoints++
                }
            }
        }
        return ScalarIdentityStatistics(compactPoints, compactNormal, compactDemand, compactFlow, compactTaint,
            protectedNormal, protectedDemand, fullPoints, counters.promotedPoints, counters.firstFullPoints,
            bitWords, fullArrayCapacity, counters.fallbackReasons.toMap())
    }

    /** Test view of all complete stored values at a statement. */
    fun edgesAt(node: P, premise: PremiseKey? = null): Sequence<Pair<PremiseKey, Facts>> = sequence {
        m.cancellation.checkpoint()
        val index = pointIndex(node)
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
            val rows = groups[key] ?: continue
            val group = rows.full?.get(index)
            if (group != null) {
                for (value in group.all()) {
                    m.cancellation.checkpoint()
                    yield(key to value)
                }
            } else for (layer in Layer.entries) {
                m.cancellation.checkpoint()
                for (protected in listOf(false, true)) if (rows.present(layer, index, protected))
                    yield(key to initialImage(m, checkNotNull(rows.initial), layer, protected))
            }
        }
    }

    /** Full leaf matching returns the whole stored value, including its off-query leaves. */
    fun edgesAt(node: P, pattern: Pattern): Sequence<Pair<PremiseKey, Facts>> = sequence {
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

/** End-state gauges and separately named cumulative promotion counters. */
data class ScalarIdentityStatistics(
    /** Unique (premise, producing statement) cells, independent of layer. */
    val compactPoints: Long,
    /** The next four gauges count point-layer memberships. */
    val compactNormal: Long,
    val compactDemand: Long,
    val compactFlow: Long,
    val compactTaint: Long,
    val protectedNormal: Long,
    val protectedDemand: Long,
    val fullPoints: Long,
    val promotedPoints: Long,
    val firstFullPoints: Long,
    val bitWords: Long,
    val fullArrayCapacity: Long,
    val fallbackReasons: Map<String, Long>,
)

/** Compatibility directory for the unchanged no-loop method path. */
class MethodEdgeStore(m: ApManager, method: MethodKey, lm: LanguageManager,
                      fieldLimit: Int, flowBacked: Boolean = false,
                      collectStatistics: Boolean = false) : ScopedEdgeStore<CommonInst>(
    m,
    object : PointDirectory<CommonInst> {
        override val size = lm.getMaxInstIndex(method.method) + 1
        override fun index(point: CommonInst): Int = lm.getInstIndex(point)
    },
    fieldLimit, flowBacked, collectStatistics,
)

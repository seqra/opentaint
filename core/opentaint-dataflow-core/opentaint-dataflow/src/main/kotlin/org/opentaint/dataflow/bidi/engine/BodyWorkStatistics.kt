package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.graph.CompactGraph
import org.opentaint.dataflow.util.Cancellation
import java.util.ArrayDeque
import java.util.IdentityHashMap

/** Optional numeric observer. It retains no fact, premise, graph, or trie node.
 * Point counts are exact packet events. Membership counts are sampled packet
 * annotations, not retained-set sizes. A cyclic SCC is not a provenance trace. */
internal class BodyWorkStatistics(graph: CompactGraph, private val cancellation: Cancellation) {
    private val components = diagnosticComponents(graph)
    private val counts = LongArray(3)
    private val points = Array(3) { LongArray(graph.size) }
    private val depths = Array(3) { LongArray(17) }
    private val kinds = Array(3) { LongArray(3) }
    private val sampled = LongArray(3)
    private val memberships = LongArray(3)
    private val protected = LongArray(3)
    private val samples = ArrayDeque<BodyWorkSample>()
    private var dropped = 0L
    private var saturated = false
    val candidatePackets: Long get() = counts[2]

    fun processed(index: Int, premise: PremiseKey, facts: Facts) = observe(0, index, premise, facts)
    fun fresh(index: Int, premise: PremiseKey, facts: Facts) = observe(1, index, premise, facts)
    fun candidate(premise: PremiseKey, facts: Facts) = observe(2, -1, premise, facts)

    private fun observe(stage: Int, index: Int, premise: PremiseKey, facts: Facts) {
        val ordinal = ++counts[stage]
        if (index >= 0) points[stage][index]++
        val root = when (facts) { is Reach -> null; is FlowTree -> facts.root; is TaintTree -> facts.root }
        val depth = root?.boundedDepth ?: 0
        depths[stage][minOf(16, depth)]++
        val kind = when (facts) { is Reach -> 0; is FlowTree -> 1; is TaintTree -> 2 }
        kinds[stage][kind]++
        if (ordinal > 16 && ordinal % 1024L != 0L) return
        cancellation.checkpoint()
        val ordinary = when (facts) {
            is Reach -> 1L
            is FlowTree -> count(facts.root) { if (it.isEmpty) 0 else 1 }
            is TaintTree -> count(facts.root) { it.exact.size.toLong() + it.any.size }
        }
        val protection = if (facts is TaintTree && facts.nonSubsumable != null)
            count(facts.nonSubsumable) { it.exact.size.toLong() + it.any.size } else 0L
        if (ordinary == null || protection == null) { dropped++; return }
        sampled[stage]++
        memberships[stage] = sum(memberships[stage], ordinary)
        protected[stage] = sum(protected[stage], protection)
        val tail = when (facts) { is Reach -> "ZERO"; is FlowTree -> facts.tail.name; is TaintTree -> facts.anyTail.name }
        val base = when (facts.base) { AccessPathBase.Zero -> "ZERO"; AccessPathBase.ClassStatic -> "STATIC"; else -> facts.base.javaClass.simpleName }
        val initial = when { premise.isZero -> "ZERO"; premise is PremiseSet -> "ND"; premise.isFlow -> "FLOW"; else -> "TAINT" }
        var node = root
        val path = ArrayList<Int>()
        while (node != null && path.size < 12 && node.accessorData != null) {
            path += node.accessorData[0]
            node = node.childData!![0]
        }
        val leaf = node?.leaf
        val markIds = if (leaf is TaintLeaves)
            (leaf.exact.data.take(2) + leaf.any.data.take(2)).distinct() else emptyList()
        val origins = (0 until minOf(4, premise.size)).map { ordinal ->
            val member = premise.member(ordinal)
            BodyWorkInitial(member.base.toString().take(100), member.pathArray.take(12), member.tail,
                (member.mark as? MarkSlot.Concrete)?.mark?.id,
                (member.exclusion as? ExclusionSet.Concrete)?.ids?.take(8) ?: emptyList())
        }
        if (samples.size == 64) samples.removeFirst()
        samples.addLast(BodyWorkSample(stage, index, if (index < 0) -1 else components.first[index],
            index >= 0 && components.second[index], initial, base, kind, facts.layer, tail, depth,
            ordinary, protection, path.toList(), origins, premise.size > 4, markIds))
    }

    private class Frame<P : TrieLeaf>(val node: TrieNode<P>, var next: Int = 0)
    private fun <P : TrieLeaf> count(root: TrieNode<P>, weight: (P) -> Long): Long? {
        val memo = IdentityHashMap<TrieNode<P>, Long>()
        val stack = ArrayDeque<Frame<P>>()
        stack.addLast(Frame(root))
        while (stack.isNotEmpty()) {
            cancellation.checkpoint()
            if (memo.size + stack.size > 4096) return null
            val frame = stack.peekLast()
            val children = frame.node.childData
            if (children != null && frame.next < children.size) {
                val child = children[frame.next++]
                if (!memo.containsKey(child)) stack.addLast(Frame(child))
                continue
            }
            var result = weight(frame.node.leaf)
            children?.forEach { result = sum(result, memo.getValue(it)) }
            memo[frame.node] = result
            stack.removeLast()
        }
        return memo.getValue(root)
    }

    private fun sum(a: Long, b: Long): Long = if (Long.MAX_VALUE - a < b) {
        saturated = true; Long.MAX_VALUE
    } else a + b

    fun snapshot(): BodyWorkSnapshot = BodyWorkSnapshot(counts.toList(), depths.map { it.toList() },
        kinds.map { it.toList() }, sampled.toList(), memberships.toList(), protected.toList(), dropped,
        saturated, points[0].indices.filter { components.second[it] }.sumOf { points[0][it] },
        points[1].indices.filter { components.second[it] }.sumOf { points[1][it] },
        points[0].indices.sortedByDescending { points[0][it] + points[1][it] }.take(12).map { index ->
            BodyWorkPoint(index, components.first[index], components.second[index], points[0][index], points[1][index])
        }, samples.toList())
}

internal data class BodyWorkPoint(val point: Int, val component: Int, val cyclic: Boolean,
                                  val processed: Long, val fresh: Long)
internal data class BodyWorkInitial(val base: String, val path: List<Int>, val tail: Tail,
    val concreteMark: Int?, val exclusions: List<Int>)
internal data class BodyWorkSample(val stage: Int, val point: Int, val component: Int, val cyclic: Boolean,
    val originalKind: String, val baseKind: String, val factsKind: Int, val layer: Layer, val tail: String,
    val maxDepth: Int, val memberships: Long, val protectedMemberships: Long, val firstPath: List<Int>,
    val initials: List<BodyWorkInitial>, val omittedInitials: Boolean, val exampleMarkIds: List<Int>)
internal data class BodyWorkSnapshot(val packets: List<Long>, val maximumDepthBins: List<List<Long>>,
    val kindPackets: List<List<Long>>, val sampledPackets: List<Long>, val sampledMemberships: List<Long>,
    val sampledProtected: List<Long>, val droppedSamples: Long, val saturated: Boolean,
    val cyclicProcessedPackets: Long, val cyclicFreshPackets: Long,
    val topPoints: List<BodyWorkPoint>, val samples: List<BodyWorkSample>) {
    val processedPackets: Long get() = packets[0]
    val freshPackets: Long get() = packets[1]
    val candidatePackets: Long get() = packets[2]
}

/** Iterative Kosaraju on the selected directed CFG. Graph state does not escape. */
internal fun diagnosticComponents(graph: CompactGraph): Pair<IntArray, BooleanArray> {
    val seen = BooleanArray(graph.size)
    val order = ArrayList<Int>(graph.size)
    val todo = ArrayDeque<Int>()
    for (start in 0 until graph.size) {
        if (seen[start]) continue
        todo.addLast(start)
        while (todo.isNotEmpty()) {
            val item = todo.removeLast()
            if (item < 0) { order += item.inv(); continue }
            if (seen[item]) continue
            seen[item] = true
            todo.addLast(item.inv())
            graph.forEachSuccessor(item) { if (!seen[it]) todo.addLast(it) }
        }
    }
    val component = IntArray(graph.size) { -1 }
    val sizes = ArrayList<Int>()
    for (start in order.asReversed()) {
        if (component[start] >= 0) continue
        val id = sizes.size
        var size = 0
        todo.addLast(start)
        component[start] = id
        while (todo.isNotEmpty()) {
            val item = todo.removeLast()
            size++
            graph.forEachPredecessor(item) { next ->
                if (component[next] < 0) { component[next] = id; todo.addLast(next) }
            }
        }
        sizes += size
    }
    val cyclic = BooleanArray(graph.size) { sizes[component[it]] > 1 }
    for (index in 0 until graph.size) graph.forEachSuccessor(index) { if (it == index) cyclic[index] = true }
    return component to cyclic
}

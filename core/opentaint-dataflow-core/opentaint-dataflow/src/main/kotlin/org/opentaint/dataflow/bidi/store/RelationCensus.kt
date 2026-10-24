package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.util.Cancellation
import java.util.ArrayDeque
import java.util.IdentityHashMap

/** Current stored output annotations, not a history or a count of concrete
 * locations denoted by ANY. Shared DAG branches count at every field path.
 * Exact and ANY annotations are separate memberships. Scalar rows count one
 * stored TaintTree header/payload, including ZERO-origin concrete output.
 * Packed rows use one geometry plus exact masks and are counted directly. */
data class RelationCensus(
    val concreteOutputMemberships: Long = 0,
    val protectedOutputMemberships: Long = 0,
    val diagonalGeometryRows: Long = 0,
    val diagonalMarkRows: Long = 0,
    val scalarConcreteRows: Long = 0,
    val flowOutputAnnotations: Long = 0,
) {
    operator fun plus(other: RelationCensus): RelationCensus = RelationCensus(
        Math.addExact(concreteOutputMemberships, other.concreteOutputMemberships),
        Math.addExact(protectedOutputMemberships, other.protectedOutputMemberships),
        Math.addExact(diagonalGeometryRows, other.diagonalGeometryRows),
        Math.addExact(diagonalMarkRows, other.diagonalMarkRows),
        Math.addExact(scalarConcreteRows, other.scalarConcreteRows),
        Math.addExact(flowOutputAnnotations, other.flowOutputAnnotations),
    )

    companion object { val ZERO = RelationCensus() }
}

/** A completion-scan local cache. No node reference escapes into the returned
 * numeric result or remains on a store after census() returns. */
internal class RelationCensusCounter(private val cancellation: Cancellation) {
    private val flow = IdentityHashMap<FlowNode, Long>()
    private val taint = IdentityHashMap<TaintNode, Long>()
    init { cancellation.checkpoint() }

    fun flowAnnotations(root: FlowNode): Long = count(root, flow) { if (it.isEmpty) 0L else 1L }
    fun concreteMemberships(root: TaintNode): Long = count(root, taint) {
        it.exact.size.toLong() + it.any.size.toLong()
    }

    fun scalar(facts: Facts): RelationCensus {
        cancellation.checkpoint()
        return when (facts) {
            is Reach -> RelationCensus.ZERO
            is FlowTree -> RelationCensus(flowOutputAnnotations = flowAnnotations(facts.root))
            is TaintTree -> RelationCensus(
                concreteOutputMemberships = concreteMemberships(facts.root),
                protectedOutputMemberships = facts.nonSubsumable?.let(::concreteMemberships) ?: 0L,
                scalarConcreteRows = 1,
            )
        }
    }

    private class Frame<P : TrieLeaf>(val node: TrieNode<P>, var next: Int = 0)
    private fun <P : TrieLeaf> count(root: TrieNode<P>, memo: IdentityHashMap<TrieNode<P>, Long>,
                                    weight: (P) -> Long): Long {
        cancellation.checkpoint()
        memo[root]?.let { return it }
        val stack = ArrayDeque<Frame<P>>()
        stack.addLast(Frame(root))
        while (stack.isNotEmpty()) {
            cancellation.checkpoint()
            val frame = stack.peekLast()
            val children = frame.node.childData
            if (children != null && frame.next < children.size) {
                val child = children[frame.next++]
                if (!memo.containsKey(child)) stack.addLast(Frame(child))
                continue
            }
            var result = weight(frame.node.leaf)
            children?.forEach { child ->
                cancellation.checkpoint()
                // The same cached child can occur under two accessors. Add its
                // count twice: those accessors denote two different paths.
                result = Math.addExact(result, memo.getValue(child))
            }
            memo[frame.node] = result
            stack.removeLast()
        }
        return memo.getValue(root)
    }
}

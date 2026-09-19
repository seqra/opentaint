package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * `minDepthToAccessor` must be the length of the shortest path down to the accessor, and `-1`
 * exactly when `containsAccessorDeep` is false.
 *
 * The unfold handler ranks the accessors it may answer with by this number and answers with one
 * of them, so a depth that is off by a level picks a different field to unfold -- a silently
 * different analysis, not a crash. Two things make it easy to get wrong and are what this pins:
 *
 *  * the nodes are a DAG, so the walk needs a memo, and the obvious memo to copy is
 *    `containsAccessorDeep`'s *visited set*, which answers "already on this search" rather than
 *    "the distance from here" and so reports a shared node's second arrival as a miss;
 *  * `[any]` stands for any number of accessors, so it costs nothing -- charging it a step would
 *    put a mark one field below an `[any]` further away than one two fields below a concrete
 *    prefix, and the handler would unfold the wrong one.
 *
 * The shapes are built out of nodes directly rather than by prepending accessors: prepending
 * applies the field-access limit, which silently truncates anything deep enough to be
 * interesting here.
 */
class AccessNodeMinDepthToAccessorTest {

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val base = AccessPathBase.This

    private val fields = (0 until 6).map { FieldAccessor("C$it", "f$it", "C${(it + 1) % 6}") }
    private val marks = (0 until 3).map { TaintMarkAccessor("m$it") }

    /** What may appear at a non-terminal position: a mark only attaches to the leaf. */
    private val inner: List<Accessor> = fields + listOf(ElementAccessor, AnyAccessor)

    /** Every accessor the walk is asked about, including ones absent from the tree. */
    private val probes: List<Accessor> =
        inner + marks + FieldAccessor("Z", "absent", "Z") + TaintMarkAccessor("absent")

    private fun idx(accessor: Accessor) = with(manager) { accessor.idx }

    private fun node(vararg children: Pair<Accessor, AccessNode>): AccessNode = with(manager) {
        val sorted = children.sortedBy { idx(it.first) }
        create(
            isAbstract = false, isFinal = false, deepAccessorExclusion = null,
            accessors = sorted.map { idx(it.first) }.toIntArray(),
            accessorNodes = sorted.map { it.second }.toTypedArray()
        )
    }

    /** `accessors` in order, ending on a final leaf. */
    private fun chain(vararg accessors: Accessor): AccessNode =
        accessors.foldRight(manager.finalNode) { accessor, tail -> node(accessor to tail) }

    private fun merge(vararg nodes: AccessNode): AccessNode =
        nodes.reduce { left, right -> left.mergeAdd(right, foldToAny = false) }

    private fun deltaOf(node: AccessNode): FinalFactAp.Delta =
        AccessTree(manager, base, node, ExclusionSet.Empty)
            .delta(manager.mostAbstractInitialAp(base))
            .single { !it.isEmpty }

    /**
     * The definition, spelled out over the same structure `containsAccessorDeep` walks:
     * enumerate the paths, take the shortest one that ends on [target]. No memo, so it costs
     * paths rather than nodes -- which is the point, since the memo is what it has to check.
     */
    private fun reference(node: AccessNode, target: Accessor, budget: Int): Int {
        if (budget == 0) return -1

        val targetIdx = idx(target)
        var best = -1

        node.forEachAccessor { accessor, child ->
            val depth = when {
                // never a match, and free to step through
                accessor == ANY_ACCESSOR_IDX -> reference(child, target, budget - 1)
                accessor == targetIdx -> 1
                else -> reference(child, target, budget - 1).let { if (it < 0) it else it + 1 }
            }

            if (depth >= 0 && (best < 0 || depth < best)) best = depth
        }

        return best
    }

    private fun assertAgrees(root: AccessNode) {
        val delta = deltaOf(root)
        for (probe in probes) {
            val expected = reference(root, probe, budget = 32)

            assertEquals(expected, delta.minDepthToAccessor(probe), "wrong depth to $probe in $root")
            assertEquals(
                expected >= 0, delta.containsAccessorDeep(probe),
                "depth and membership disagree on $probe in $root"
            )
        }
    }

    @Test
    fun `a chain reports the position of every accessor on it`() {
        val delta = deltaOf(chain(fields[0], fields[1], fields[2], marks[0]))

        assertEquals(1, delta.minDepthToAccessor(fields[0]))
        assertEquals(2, delta.minDepthToAccessor(fields[1]))
        assertEquals(3, delta.minDepthToAccessor(fields[2]))
        assertEquals(4, delta.minDepthToAccessor(marks[0]))
        assertEquals(-1, delta.minDepthToAccessor(marks[1]))
    }

    @Test
    fun `any costs nothing`() {
        // `[any]` stands for an unknown number of accessors, so a mark below it is as near as
        // this structure can claim -- the same distance as a mark directly under the root.
        assertEquals(1, deltaOf(chain(marks[0])).minDepthToAccessor(marks[0]))
        assertEquals(1, deltaOf(chain(AnyAccessor, marks[0])).minDepthToAccessor(marks[0]))
        assertEquals(1, deltaOf(chain(AnyAccessor, AnyAccessor, marks[0])).minDepthToAccessor(marks[0]))
        assertEquals(2, deltaOf(chain(AnyAccessor, fields[0], marks[0])).minDepthToAccessor(marks[0]))
        assertEquals(2, deltaOf(chain(fields[0], AnyAccessor, marks[0])).minDepthToAccessor(marks[0]))
    }

    @Test
    fun `the any accessor is never itself a match`() {
        // It is the abstraction the request is asking to see through, so it is not an answer.
        assertEquals(-1, deltaOf(chain(AnyAccessor, marks[0])).minDepthToAccessor(AnyAccessor))
    }

    @Test
    fun `the shortest of two branches wins`() {
        val near = chain(fields[0], fields[1], marks[0])
        val far = chain(fields[2], fields[3], fields[4], marks[0])

        assertEquals(3, deltaOf(merge(near, far)).minDepthToAccessor(marks[0]))
        assertEquals(3, deltaOf(merge(far, near)).minDepthToAccessor(marks[0]))
    }

    @Test
    fun `a shared node is measured from every parent`() {
        // The same tail under a one-field prefix and under a three-field one. The merge reuses
        // the tail node under both, so the second arrival lands on a node the walk has already
        // answered for -- and what it cached is the distance from that node, not from the root,
        // so it stays correct. A visited set in the same place would report the second arrival
        // as a miss and leave the deeper branch as the only answer.
        val tail = listOf(fields[5], marks[0])
        val shallow = chain(fields[0], *tail.toTypedArray())
        val deep = chain(fields[1], fields[2], fields[3], *tail.toTypedArray())

        assertEquals(3, deltaOf(merge(deep, shallow)).minDepthToAccessor(marks[0]))
        assertEquals(3, deltaOf(merge(shallow, deep)).minDepthToAccessor(marks[0]))
    }

    private fun randomChain(random: Random): AccessNode {
        val prefix = List(1 + random.nextInt(5)) { inner[random.nextInt(inner.size)] }
        val mark = marks.getOrNull(random.nextInt(marks.size + 1))
        return chain(*(prefix + listOfNotNull(mark)).toTypedArray())
    }

    @Test
    fun `agrees with the definition on single chains`() {
        for (seed in 0 until 300) {
            assertAgrees(randomChain(Random(seed)))
        }
    }

    @Test
    fun `agrees with the definition on merged trees with shared subtrees`() {
        for (seed in 0 until 150) {
            val random = Random(seed)

            // A shared tail under several different prefixes: the merge result reuses the same
            // node object at several depths, which is the DAG the memo has to handle.
            val tail = List(1 + random.nextInt(3)) { inner[random.nextInt(inner.size)] } +
                marks[random.nextInt(marks.size)]

            var merged = randomChain(random)
            repeat(4) {
                val prefix = List(1 + random.nextInt(3)) { inner[random.nextInt(inner.size)] }
                merged = merge(merged, chain(*(prefix + tail).toTypedArray()))
            }

            assertAgrees(merged)
        }
    }

    @Test
    fun `agrees with the definition on deep self-similar shapes`() {
        // The shape the unfold demand actually walks: one field repeated, with an `[any]` and a
        // mark at the bottom, merged with its own prefixes so nodes are shared at every level.
        val f = fields[0]
        var root = chain(*(List(12) { f } + marks[0]).toTypedArray())
        for (depth in 1 until 12) {
            root = merge(root, chain(*(List(depth) { f } + listOf(AnyAccessor, marks[1])).toTypedArray()))
        }

        assertAgrees(root)
    }
}

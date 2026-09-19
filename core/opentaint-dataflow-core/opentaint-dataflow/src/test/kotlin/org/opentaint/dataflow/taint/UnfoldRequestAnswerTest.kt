package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * What an unfold request is answered with.
 *
 * The answer is the set of accessors the asking frame unfolds its `[any]` on, and every one of
 * them spawns an abstraction there that raises unfold requests of its own -- so the size of the
 * answer is a branching factor, applied once per frame the demand passes through, and the
 * selection is the one thing keeping it at one.
 *
 * Which one is picked is therefore analysis-visible: a different choice reports a different set
 * of flows. These pin the rule -- nearest mark first, least accessor on a tie -- and in
 * particular that it does not depend on the order the delta happens to enumerate its children,
 * since that order comes out of merges whose sequence nothing controls.
 */
class UnfoldRequestAnswerTest {

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val base = AccessPathBase.This

    private val fields = (0 until 6).map { FieldAccessor("C$it", "f$it", "C${(it + 1) % 6}") }
    private val mark = TaintMarkAccessor("wanted")
    private val otherMark = TaintMarkAccessor("other")

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

    private fun answer(node: AccessNode): List<Accessor> =
        deltaOf(node).markCandidates(mark).selectAnswer(mark, extraPaths = 0)

    private fun widenedAnswer(node: AccessNode, extraPaths: Int = 2): List<Accessor> =
        deltaOf(node).markCandidates(mark).selectAnswer(mark, extraPaths)

    @Test
    fun `the mark itself is the answer when it is a start accessor`() {
        assertEquals(listOf(mark), answer(chain(mark)))
    }

    @Test
    fun `the nearer field wins`() {
        val near = chain(fields[4], mark)
        val far = chain(fields[0], fields[1], mark)

        // f0 is the least accessor, and it is not the answer: depth is ranked first
        assertEquals(listOf(fields[4]), answer(merge(near, far)))
        assertEquals(listOf(fields[4]), answer(merge(far, near)))
    }

    @Test
    fun `the least accessor breaks a tie, whatever order the delta enumerates`() {
        val left = chain(fields[0], fields[5], mark)
        val right = chain(fields[3], fields[2], mark)

        assertEquals(listOf(fields[0]), answer(merge(left, right)))
        assertEquals(listOf(fields[0]), answer(merge(right, left)))
    }

    @Test
    fun `a field that does not lead to the mark is not a candidate`() {
        // f0 is nearer and lesser, and carries a different mark: ranking happens among the
        // accessors that reach the requested mark, not among all of them.
        val decoy = chain(fields[0], otherMark)
        val real = chain(fields[3], fields[4], mark)

        assertEquals(listOf(fields[3]), answer(merge(decoy, real)))
    }

    @Test
    fun `an any start accessor answers with its successors, never with itself`() {
        // `[any]` is the abstraction the request is asking to see through -- answering with it
        // would ask the asking frame to unfold on the thing it is already abstracting.
        assertEquals(listOf(fields[2]), answer(chain(AnyAccessor, fields[2], mark)))
    }

    @Test
    fun `a mark under an any is as near as one at the top`() {
        // `[any]` costs nothing, so the two candidates tie on depth and the least accessor wins.
        val underAny = chain(AnyAccessor, fields[5], mark)
        val direct = chain(fields[1], mark)

        assertEquals(listOf(fields[1]), answer(merge(underAny, direct)))
    }

    @Test
    fun `a delta without the mark has no answer`() {
        assertEquals(emptyList(), answer(chain(fields[0], fields[1], otherMark)))
        assertEquals(emptyList(), widenedAnswer(chain(fields[0], fields[1], otherMark)))
    }

    @Test
    fun `widening adds the paths that overlap the chosen one least`() {
        // Three ways to the mark. f1 is nearest and goes first. Of the rest, one re-walks f5 --
        // which f1's path already covers -- and the other walks nothing in common, so the
        // disjoint one is preferred even though its accessor is greater and it is no nearer.
        val chosen = chain(fields[1], fields[5], mark)
        val overlapping = chain(fields[2], fields[5], mark)
        val disjoint = chain(fields[3], fields[4], mark)

        assertEquals(
            listOf(fields[1], fields[3], fields[2]),
            widenedAnswer(merge(chosen, overlapping, disjoint))
        )
    }

    @Test
    fun `widening stops at the paths that exist`() {
        val only = chain(fields[1], mark)

        assertEquals(listOf(fields[1]), widenedAnswer(only))
        assertEquals(listOf(fields[1], fields[3]), widenedAnswer(merge(only, chain(fields[3], mark))))
    }

    @Test
    fun `widening never drops the nearest`() {
        val near = chain(fields[4], mark)
        val far = chain(fields[0], fields[1], mark)

        assertEquals(fields[4], widenedAnswer(merge(near, far)).first())
    }

    @Test
    fun `every candidate is reported, and only the selection narrows them`() {
        // The candidates are the complete answer; what makes the demand finite is the choice
        // among them. Keeping the two apart is what lets the selection be widened later without
        // touching what counts as a place the mark may be.
        val delta = deltaOf(merge(chain(fields[4], mark), chain(fields[0], fields[1], mark)))
        val candidates = delta.markCandidates(mark)

        assertEquals(
            // the accessor itself is a step, and so is the mark
            mapOf(fields[4] as Accessor to 2, fields[0] as Accessor to 3),
            candidates.associate { it.accessor to it.depth }
        )
        assertEquals(1, candidates.selectAnswer(mark, extraPaths = 0).size)
    }
}

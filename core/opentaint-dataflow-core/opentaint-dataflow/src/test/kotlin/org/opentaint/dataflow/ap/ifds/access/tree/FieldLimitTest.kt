package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import java.util.IdentityHashMap
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue
import kotlin.test.fail

class FieldLimitTest {
    private companion object {
        val A = FieldAccessor("C", "a", "C")
        val B = FieldAccessor("C", "b", "C")
        val C = FieldAccessor("C", "c", "C")
        val D = FieldAccessor("C", "d", "C")
        val E = FieldAccessor("C", "e", "C")
        val F = FieldAccessor("C", "f", "C")
        val NC = FieldAccessor("C", "<rule-storage>", "C")
        val MARK = TaintMarkAccessor("m")
        val TYPE = TypeInfoAccessor("T")
        val STATIC = ClassStaticAccessor("S")
        val EL = ElementAccessor
        val ANY = AnyAccessor

        val COVERED = listOf(A, B, C, D, E, F, EL)
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            (accessor is FieldAccessor && accessor != NC) || accessor is ElementAccessor
    }

    private val base = AccessPathBase.This

    private fun manager(limit: Int) = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), fieldLimit = limit)

    private fun TreeApManager.idx(accessor: Accessor) = with(this) { accessor.idx }

    /** A raw chain, built without any normalization or limit; the last accessor may be [FinalAccessor]. */
    private fun TreeApManager.chain(vararg accessors: Accessor): AccessNode {
        val final = accessors.lastOrNull() == FinalAccessor
        val path = if (final) accessors.dropLast(1) else accessors.toList()
        return path.foldRight(if (final) finalNode else abstractNode) { accessor, node ->
            create(isAbstract = false, isFinal = false, null, intArrayOf(idx(accessor)), arrayOf(node))
        }
    }

    private fun TreeApManager.node(vararg edges: Pair<Accessor, AccessNode>, final: Boolean = false): AccessNode {
        val sorted = edges.sortedBy { idx(it.first) }
        return create(
            isAbstract = false, isFinal = final, null,
            IntArray(sorted.size) { idx(sorted[it].first) }, Array(sorted.size) { sorted[it].second },
        )
    }

    private fun TreeApManager.merge(vararg nodes: AccessNode): AccessNode =
        nodes.reduce { acc, n -> acc.mergeAdd(n, foldToAny = false) }

    private fun TreeApManager.finalTree(vararg accessors: Accessor): AccessTree =
        accessors.foldRight(createFinalAp(base, ExclusionSet.Empty)) { a, f -> f.prependAccessor(a) } as AccessTree

    private fun TreeApManager.abstractTree(vararg accessors: Accessor): AccessTree =
        accessors.foldRight(mostAbstractFinalAp(base)) { a, f -> f.prependAccessor(a) } as AccessTree

    private fun TreeApManager.initial(vararg accessors: Accessor): AccessPath =
        accessors.foldRight(mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) } as AccessPath

    /* ---------- result invariants ---------- */

    private class LeafPath(val accessors: List<Int>, val final: Boolean)

    private fun AccessNode.leafPaths(): List<LeafPath> {
        val result = mutableListOf<LeafPath>()
        fun walk(node: AccessNode, prefix: List<Int>) {
            if (node.isFinal) result += LeafPath(prefix, final = true)
            if (node.isAbstract) result += LeafPath(prefix, final = false)
            node.forEachAccessor { accessor, child -> walk(child, prefix + accessor) }
        }
        walk(this, emptyList())
        return result
    }

    private fun TreeApManager.countedOnPath(path: List<Int>): Int =
        path.count { (with(this) { it.accessor } is FieldAccessor || it == idx(EL)) && isCoveredByAny(it) }

    private fun TreeApManager.isCovered(accessor: Int) = UnrollStrategy.unrollAccessor(with(this) { accessor.accessor })

    private fun AccessNode.child(accessor: Int): AccessNode? {
        var result: AccessNode? = null
        forEachAccessor { a, child -> if (a == accessor) result = child }
        return result
    }

    // Semantic match: an [any] edge matches zero or more covered accessors
    private fun TreeApManager.covers(node: AccessNode, path: LeafPath, i: Int = 0): Boolean {
        val anyChild = node.getAnyChild()
        if (anyChild != null && coversUnderAny(anyChild, path, i)) return true

        if (i == path.accessors.size) return if (path.final) node.isFinal else node.isAbstract

        val child = node.child(path.accessors[i]) ?: return false
        return covers(child, path, i + 1)
    }

    private fun TreeApManager.coversUnderAny(anyChild: AccessNode, path: LeafPath, i: Int): Boolean {
        if (covers(anyChild, path, i)) return true
        if (i == path.accessors.size || !isCovered(path.accessors[i])) return false
        return coversUnderAny(anyChild, path, i + 1)
    }

    // An [any] of the original path is checked through a few of its concretizations
    private fun TreeApManager.concretizations(path: LeafPath): List<LeafPath> {
        val anyIdx = path.accessors.indexOf(idx(ANY))
        if (anyIdx < 0) return listOf(path)
        val prefix = path.accessors.subList(0, anyIdx)
        val suffix = path.accessors.subList(anyIdx + 1, path.accessors.size)
        return listOf(emptyList(), listOf(idx(F)), listOf(idx(E), idx(EL))).map {
            LeafPath(prefix + it + suffix, path.final)
        }
    }

    private fun TreeApManager.checkLimited(original: AccessNode, limited: AccessNode, sound: Boolean = true) {
        assertTrue(limited.boundedDepth <= fieldLimit, "boundedDepth ${limited.boundedDepth} > $fieldLimit: $limited")

        val independentDepth = IdentityHashMap<AccessNode, Int>()
        fun depth(node: AccessNode): Int = independentDepth.getOrPut(node) {
            var d = 0
            node.forEachAccessor { accessor, child ->
                val counted = (with(this) { accessor.accessor } is FieldAccessor || accessor == idx(EL)) && isCovered(accessor)
                d = maxOf(d, depth(child) + if (counted) 1 else 0)
            }
            d
        }
        assertEquals(depth(limited), limited.boundedDepth)

        for (path in limited.leafPaths()) {
            assertTrue(countedOnPath(path.accessors) <= fieldLimit, "Path over the limit in $limited")
            assertTrue(path.accessors.count { it == idx(ANY) } <= 1, "Two [any] on a path of $limited")
        }

        if (!sound) return
        for (path in original.leafPaths()) {
            for (concrete in concretizations(path)) {
                if (!covers(limited, concrete)) {
                    fail("$limited does not cover ${concrete.accessors.map { with(this) { it.accessor } }} of $original")
                }
            }
        }
    }

    private fun TreeApManager.limited(original: AccessNode, sound: Boolean = true): AccessNode =
        original.limitFields().also { checkLimited(original, it, sound) }

    /* ---------- counted accessors ---------- */

    @Test
    fun `user example via prepends`() = with(manager(2)) {
        val tree = finalTree(STATIC, B, C, D, MARK)
        assertEquals(chain(STATIC, B, C, ANY, MARK, FinalAccessor), tree.access)
        checkLimited(chain(STATIC, B, C, D, MARK, FinalAccessor), tree.access)
    }

    @Test
    fun `element accessors are counted`() = with(manager(2)) {
        assertEquals(chain(A, EL, ANY, FinalAccessor), finalTree(A, EL, B).access)
        assertEquals(chain(EL, EL, ANY, FinalAccessor), finalTree(EL, EL, A).access)
    }

    @Test
    fun `non covered field type info and taint mark are not counted`() = with(manager(2)) {
        val withNc = chain(A, NC, B, FinalAccessor)
        assertSame(withNc, withNc.limitFields())
        assertEquals(chain(A, NC, B, ANY, FinalAccessor), limited(chain(A, NC, B, C, FinalAccessor)))
        assertEquals(chain(NC, A, B, ANY, FinalAccessor), finalTree(NC, A, B, C).access)

        val suffix = chain(A, B, C, TYPE, MARK, FinalAccessor)
        assertEquals(chain(A, B, ANY, TYPE, MARK, FinalAccessor), limited(suffix))
        assertEquals(chain(A, TYPE, B, MARK, FinalAccessor), finalTree(A, TYPE, B, MARK).access)
    }

    @Test
    fun `accessors between the cut and the last counted one are absorbed`() = with(manager(2)) {
        assertEquals(chain(A, B, ANY, FinalAccessor), limited(chain(A, B, C, D, TYPE, E, FinalAccessor), sound = false))
    }

    @Test
    fun `non counted accessors right after the cut stay in the prefix`() = with(manager(2)) {
        assertEquals(chain(A, B, TYPE, ANY, FinalAccessor), limited(chain(A, B, TYPE, C, FinalAccessor)))
        assertEquals(chain(A, B, NC, ANY, FinalAccessor), limited(chain(A, B, NC, C, D, FinalAccessor)))
    }

    /* ---------- branches and sharing ---------- */

    @Test
    fun `only the long branch collapses`() = with(manager(2)) {
        val short = chain(E, FinalAccessor)
        val original = node(A to node(B to chain(C, D, FinalAccessor), E to short.child(idx(E))!!))
        val result = limited(original)

        assertEquals(node(A to node(B to chain(ANY, FinalAccessor), E to finalNode)), result)
        assertSame(original.child(idx(A))!!.child(idx(E)), result.child(idx(A))!!.child(idx(E)))
    }

    @Test
    fun `shared subtree reached at two depths`() = with(manager(3)) {
        val shared = chain(C, D, FinalAccessor)
        val original = node(A to shared, B to node(E to shared))
        val result = limited(original)

        assertSame(shared, result.child(idx(A)))
        assertEquals(chain(B, E, C, ANY, FinalAccessor), result.child(idx(B))?.let { node(B to it) })
    }

    @Test
    fun `sibling paths below the cut merge into one any edge`() = with(manager(1)) {
        val original = node(A to merge(chain(B, MARK, FinalAccessor), chain(C, D, FinalAccessor), finalNode))
        val expected = node(A to node(ANY to merge(chain(MARK, FinalAccessor), finalNode), final = true))
        assertEquals(expected, limited(original))
    }

    /* ---------- existing [any] ---------- */

    @Test
    fun `existing any before the cut absorbs the overflow`() = with(manager(2)) {
        assertEquals(chain(A, ANY, FinalAccessor), limited(chain(A, ANY, B, C, D, FinalAccessor)))
        assertEquals(chain(A, ANY, FinalAccessor), limited(chain(A, ANY, B, C, FinalAccessor)))

        val partial = node(A to node(ANY to merge(chain(B, FinalAccessor), chain(C, D, E, FinalAccessor))))
        assertEquals(node(A to node(ANY to merge(chain(B, FinalAccessor), finalNode))), limited(partial))
    }

    @Test
    fun `existing any after the cut`() = with(manager(2)) {
        assertEquals(chain(A, B, ANY, FinalAccessor), limited(chain(A, B, ANY, C, FinalAccessor)))
        assertEquals(chain(A, B, ANY, MARK, FinalAccessor), limited(chain(A, B, C, ANY, D, MARK, FinalAccessor)))

        val within = chain(A, B, ANY, FinalAccessor)
        assertSame(within, within.limitFields())
        val withinAny = chain(A, ANY, B, FinalAccessor)
        assertSame(withinAny, withinAny.limitFields())
    }

    @Test
    fun `cut next to an existing any edge merges into it`() = with(manager(1)) {
        val original = node(A to node(ANY to chain(B, MARK, FinalAccessor), C to chain(D, FinalAccessor)))
        assertEquals(node(A to node(ANY to merge(chain(MARK, FinalAccessor), finalNode))), limited(original))
    }

    @Test
    fun `zero limit`() = with(manager(0)) {
        assertEquals(chain(ANY, FinalAccessor), finalTree(A, B).access)
        assertEquals(chain(STATIC, ANY, MARK, FinalAccessor), finalTree(STATIC, A, MARK).access)
        assertEquals(chain(NC, ANY, FinalAccessor), finalTree(NC, A).access)
        assertEquals(chain(ANY, FinalAccessor), limited(chain(ANY, A, FinalAccessor)))

        val markOnly = finalTree(MARK).access
        assertSame(markOnly, markOnly.limitFields())
    }

    /* ---------- concat ---------- */

    @Test
    fun `concat cuts the joined path`() = with(manager(3)) {
        val delta = AccessTree.NodeAccessTreeDelta(this, finalTree(C, D).access)
        val tree = abstractTree(A, B).concat(FactTypeChecker.Dummy, delta) as AccessTree
        assertEquals(chain(A, B, C, ANY, FinalAccessor), tree.access)
        checkLimited(chain(A, B, C, D, FinalAccessor), tree.access)
    }

    @Test
    fun `concat of a delta with an any`() = with(manager(3)) {
        val delta = AccessTree.NodeAccessTreeDelta(this, chain(ANY, C, D, FinalAccessor))
        val tree = abstractTree(A, B).concat(FactTypeChecker.Dummy, delta) as AccessTree
        assertEquals(chain(A, B, ANY, FinalAccessor), tree.access)

        val nested = abstractTree(A, ANY, B).concat(FactTypeChecker.Dummy, AccessTree.NodeAccessTreeDelta(this, chain(ANY, C, FinalAccessor)))
        assertEquals(chain(A, ANY, C, FinalAccessor), (nested as AccessTree).access)
    }

    @Test
    fun `initial path concat with a tree delta`() = with(manager(2)) {
        val nodeDelta = finalTree(D).delta(initial()).single()
        val tree = initial(A, B, C).concat(FactTypeChecker.Dummy, nodeDelta) as AccessTree
        assertEquals(chain(A, B, ANY, FinalAccessor), tree.access)

        val emptyDelta = abstractTree().delta(initial()).single()
        val abstract = initial(A, B, C).concat(FactTypeChecker.Dummy, emptyDelta) as AccessTree
        assertEquals(chain(A, B, ANY), abstract.access)
    }

    /* ---------- unlimited manager ---------- */

    @Test
    fun `unlimited manager never limits and never asks the strategy`() {
        val manager = TreeApManager(ThrowingStrategy, RefManager(), Cancellation())
        with(manager) {
            val tree = finalTree(A, B, C, D, E, F, EL, EL, MARK)
            assertEquals(0, tree.access.boundedDepth)
            assertSame(tree.access, tree.access.limitFields())

            val delta = AccessTree.NodeAccessTreeDelta(this, finalTree(C, D).access)
            val concat = abstractTree(A, B, E, F).concat(FactTypeChecker.Dummy, delta) as AccessTree
            assertEquals(finalTree(A, B, E, F, C, D), concat)
        }
    }

    private object ThrowingStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = error("Strategy queried")
    }

    /* ---------- randomized ---------- */

    @Test
    fun `random trees keep every invariant`() {
        val random = Random(42)
        for (limit in 0..3) {
            val manager = manager(limit)
            repeat(300) {
                with(manager) {
                    val original = randomTree(random, depth = 0, anyAbove = false, used = emptySet())
                    limited(original)
                }
            }
        }
    }

    @Test
    fun `random prepends keep every invariant`() {
        val random = Random(7)
        for (limit in 0..3) {
            val manager = manager(limit)
            repeat(200) {
                with(manager) {
                    var tree = finalTree(MARK).access
                    repeat(random.nextInt(1, 7)) {
                        val accessor = COVERED[random.nextInt(COVERED.size)]
                        tree = merge(tree.addParent(idx(accessor)), randomTree(random, 3, anyAbove = false, used = emptySet()))
                            .limitFields()
                        checkLimited(tree, tree)
                    }
                }
            }
        }
    }

    private fun TreeApManager.randomTree(random: Random, depth: Int, anyAbove: Boolean, used: Set<Accessor>): AccessNode {
        val leaf = random.nextInt(4)
        val isFinal = leaf == 0 || leaf == 3
        val isAbstract = leaf == 1 || leaf == 3
        if (depth >= 6 || random.nextInt(3) == 0) {
            val node = create(isAbstract, isFinal)
            return if (random.nextInt(4) == 0) create(false, false, null, intArrayOf(idx(MARK)), arrayOf(create(false, true))) else node
        }

        val edges = mutableListOf<Pair<Accessor, AccessNode>>()
        for (accessor in COVERED.shuffled(random).take(random.nextInt(1, 3))) {
            if (accessor in used && accessor != EL) continue
            edges += accessor to randomTree(random, depth + 1, anyAbove, used + accessor)
        }
        if (!anyAbove && random.nextInt(5) == 0) {
            edges += ANY to randomTree(random, depth + 1, anyAbove = true, used)
        }
        if (edges.isEmpty()) return create(isAbstract = true, isFinal = false)

        val sorted = edges.sortedBy { idx(it.first) }
        return create(
            isAbstract, isFinal, null,
            IntArray(sorted.size) { idx(sorted[it].first) }, Array(sorted.size) { sorted[it].second },
        )
    }
}

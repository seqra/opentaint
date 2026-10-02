package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import java.util.IdentityHashMap
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

class AnyAccessPathTest {
    private companion object {
        val A = FieldAccessor("C", "a", "C")
        val F = FieldAccessor("C", "f", "C")
        val G = FieldAccessor("C", "g", "C")
        val H = FieldAccessor("C", "h", "C")
        val X = FieldAccessor("C", "x", "C")
        val Y = FieldAccessor("C", "y", "C")
        val NOT_COVERED = FieldAccessor("C", "nc", "C")
        val MARK = TaintMarkAccessor("m")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            (accessor is FieldAccessor && accessor != NOT_COVERED) || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val base = AccessPathBase.This

    private fun initial(vararg accessors: Accessor, exclusions: ExclusionSet = ExclusionSet.Empty): AccessPath =
        accessors.foldRight(manager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }
            .replaceExclusions(exclusions) as AccessPath

    private fun finalInitial(vararg accessors: Accessor): AccessPath =
        accessors.foldRight(manager.createFinalInitialAp(base, ExclusionSet.Empty)) { a, f -> f.prependAccessor(a) }
            as AccessPath

    /** this.<accessors>.* */
    private fun abstractTree(vararg accessors: Accessor): AccessTree =
        accessors.foldRight(manager.mostAbstractFinalAp(base)) { a, f -> f.prependAccessor(a) } as AccessTree

    /** this.<accessors>.$ */
    private fun finalTree(vararg accessors: Accessor): AccessTree =
        accessors.foldRight(manager.createFinalAp(base, ExclusionSet.Empty)) { a, f -> f.prependAccessor(a) }
            as AccessTree

    private fun merged(vararg trees: AccessTree): AccessTree =
        trees.reduce { acc, t -> AccessTree(manager, base, acc.access.mergeAdd(t.access), acc.exclusions) }

    private fun AccessTree.node(vararg accessors: Accessor): AccessTree.AccessNode =
        accessors.fold(access) { n, a -> n.getChild(with(manager) { a.idx })!! }

    private fun AccessTree.deltaNode(path: InitialFactAp): AccessTree.AccessNode? =
        delta(path).filterIsInstance<AccessTree.NodeAccessTreeDelta>().singleOrNull()?.node

    private fun AccessTree.hasEmptyDeltaFor(path: InitialFactAp): Boolean =
        delta(path).any { it.isEmpty }

    /* ---------- flags ---------- */

    @Test
    fun `tree containsAny marks only the branch with an any edge`() {
        val tree = merged(abstractTree(A, AnyAccessor, F), abstractTree(G, X))

        assertTrue(tree.access.containsAny)
        assertTrue(tree.node(A).containsAny)
        assertFalse(tree.node(G).containsAny)
        assertFalse(abstractTree(A, F).access.containsAny)
        assertFalse(manager.abstractNode.containsAny)
    }

    @Test
    fun `tree containsAny survives interning`() {
        val tree = merged(abstractTree(A, AnyAccessor, F), abstractTree(G, X))
        val interned = tree.access.internNodes(AccessTreeInterner(), IdentityHashMap())

        assertTrue(interned.interned)
        assertTrue(interned.containsAny)
        assertEquals(tree.access, interned)
        assertEquals(tree.access.hashCode(), interned.hashCode())
    }

    @Test
    fun `path containsAny and size`() {
        val path = initial(A, AnyAccessor, F).access!!
        assertTrue(path.containsAny)
        assertFalse(path.next!!.next!!.containsAny)
        assertEquals(3, path.size)
        assertEquals(2, initial(A, F).access!!.size)
        assertFalse(initial(A, F).access!!.containsAny)
    }

    @Test
    fun `serializer round trip keeps any and the flags`() {
        val serializer = TreeSerializer(manager, TestSerializationContext())

        val path = initial(A, AnyAccessor, F)
        val tree = merged(abstractTree(A, AnyAccessor, F), finalTree(G))

        val bytes = ByteArrayOutputStream()
        with(serializer) {
            DataOutputStream(bytes).use {
                it.writeInitialAp(path)
                it.writeFinalAp(tree)
            }
        }

        val (readPath, readTree) = with(serializer) {
            DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use {
                it.readInitialAp() to it.readFinalAp()
            }
        }

        assertEquals(path, readPath)
        assertTrue((readPath as AccessPath).access!!.containsAny)
        assertEquals(tree, readTree)
        assertTrue((readTree as AccessTree).access.containsAny)
        assertFalse(readTree.node(G).containsAny)
    }

    /* ---------- AccessPath with [any] ---------- */

    @Test
    fun `prepend any keeps it in the path`() {
        val path = initial(A, AnyAccessor, F)
        assertEquals(listOf(A, AnyAccessor, F), path.access!!.accessorList())
    }

    @Test
    fun `adjacent any collapses`() {
        val path = initial(A, AnyAccessor, AnyAccessor, F)
        assertEquals(listOf(A, AnyAccessor, F), path.access!!.accessorList())
    }

    @Test
    fun `trailing any is kept`() {
        val anyOnly = manager.mostAbstractInitialAp(base).prependAccessor(AnyAccessor) as AccessPath
        assertEquals(listOf<Accessor>(AnyAccessor), anyOnly.access!!.accessorList())
        assertEquals(listOf(A, AnyAccessor), initial(A, AnyAccessor).access!!.accessorList())
        assertFalse(initial(A) == initial(A, AnyAccessor))
    }

    @Test
    fun `getAllAccessors ignores any`() {
        val path = initial(A, AnyAccessor, F)
        assertEquals(setOf<Accessor>(A, F), path.getAllAccessors())

        val delta = path.delta(initial(A)).single()
        assertEquals(setOf<Accessor>(F), delta.getAllAccessors())
        assertTrue(delta.startsWithAccessor(AnyAccessor))
    }

    @Test
    fun `path operations treat any as a symbol`() {
        val path = initial(AnyAccessor, F)
        assertTrue(path.startsWithAccessor(AnyAccessor))
        assertFalse(path.startsWithAccessor(F))
        assertEquals(initial(F), path.readAccessor(AnyAccessor))
        assertNull(path.readAccessor(F))
        assertTrue(initial(A, AnyAccessor, F).delta(initial(A, F)).isEmpty())
    }

    @Test
    fun `path with any concatenates into a tree with an any edge`() {
        val path = initial(A, AnyAccessor)
        val delta = abstractTree().delta(initial()).single()
        val tree = path.concat(FactTypeChecker.Dummy, delta) as AccessTree
        assertEquals(abstractTree(A, AnyAccessor), tree)

        val nodeDelta = finalTree(F).delta(initial()).single()
        val withNode = path.concat(FactTypeChecker.Dummy, nodeDelta) as AccessTree
        assertEquals(finalTree(A, AnyAccessor, F), withNode)
    }

    /* ---------- AccessTree.delta / contains with [any] in the path: exact match ---------- */

    @Test
    fun `any in the path does not match concrete accessors`() {
        val path = initial(A, AnyAccessor, F)
        for (tree in listOf(abstractTree(A, F), abstractTree(A, G, H, F))) {
            assertTrue(tree.delta(path).isEmpty())
            assertFalse(tree.contains(path))
        }
    }

    @Test
    fun `any in the path matches the tree any edge`() {
        val tree = abstractTree(A, AnyAccessor, F)
        assertTrue(tree.hasEmptyDeltaFor(initial(A, AnyAccessor, F)))
        assertTrue(tree.contains(initial(A, AnyAccessor, F)))
        assertFalse(tree.contains(initial(A, AnyAccessor, G)))
        assertFalse(tree.contains(initial(AnyAccessor, F)))
    }

    @Test
    fun `delta through the any edge ignores concrete branches`() {
        val tree = merged(finalTree(A, AnyAccessor, F, X), finalTree(A, F, Y), finalTree(A, G, F, Y))
        assertEquals(finalTree(X).access, tree.deltaNode(initial(A, AnyAccessor, F)))
    }

    @Test
    fun `trailing any takes only the any edge subtree`() {
        val tree = merged(finalTree(A, AnyAccessor, X), finalTree(A, F))
        assertEquals(finalTree(X).access, tree.deltaNode(initial(A, AnyAccessor)))
    }

    @Test
    fun `any path matches final only through the any edge`() {
        assertTrue(finalTree(A, AnyAccessor).hasEmptyDeltaFor(finalInitial(A, AnyAccessor)))
        assertTrue(finalTree(A, AnyAccessor).contains(finalInitial(A, AnyAccessor)))
        assertTrue(finalTree(A, G).delta(finalInitial(A, AnyAccessor)).isEmpty())
        assertFalse(finalTree(A, G).contains(finalInitial(A, AnyAccessor)))
    }

    @Test
    fun `delta with any applies the exclusions`() {
        val tree = merged(finalTree(A, AnyAccessor, F, X), finalTree(A, AnyAccessor, F, Y))
        val delta = tree.deltaNode(initial(A, AnyAccessor, F, exclusions = ExclusionSet.Empty.add(X)))
        assertEquals(finalTree(Y).access, delta)
    }

    @Test
    fun `paths without any keep the old behaviour`() {
        val tree = merged(finalTree(A, F, X), abstractTree(A, G))
        assertEquals(finalTree(X).access, tree.deltaNode(initial(A, F)))
        assertTrue(tree.hasEmptyDeltaFor(initial(A, G)))
        assertTrue(tree.delta(initial(A, H)).isEmpty())
        assertTrue(tree.contains(initial(A, G)))
        assertFalse(tree.contains(initial(A, G, H)))
        assertFalse(tree.contains(initial(A, F)))
    }

    /* ---------- filterStartsWith ---------- */

    @Test
    fun `filterStartsWith with any follows the any edge exactly`() {
        val tree = merged(finalTree(A, AnyAccessor, F, X), finalTree(A, G, F, Y), finalTree(H))
        val path = initial(A, AnyAccessor, F)

        val filtered = tree.access.filterStartsWith(path.access)
        assertEquals(finalTree(A, AnyAccessor, F, X).access, filtered)

        val filteredTree = AccessTree(manager, base, filtered!!, ExclusionSet.Empty)
        assertEquals(tree.delta(path), filteredTree.delta(path))
    }

    @Test
    fun `filterStartsWith with any drops trees without an any edge`() {
        assertNull(finalTree(A, G, F).access.filterStartsWith(initial(A, AnyAccessor, F).access))
        assertNull(finalTree(A, F).access.filterStartsWith(initial(AnyAccessor, F).access))
    }

    /* ---------- syntactic operations ---------- */

    @Test
    fun `equalTo is syntactic`() {
        assertTrue(abstractTree(A, AnyAccessor, F).equalTo(initial(A, AnyAccessor, F)))
        assertFalse(abstractTree(A, G, F).equalTo(initial(A, AnyAccessor, F)))
        assertFalse(abstractTree(A, AnyAccessor, F).equalTo(initial(A, F)))
        assertTrue(abstractTree(A, F).equalTo(initial(A, F)))
    }

    @Test
    fun `splitDelta follows the raw any edge`() {
        val path = initial(A, AnyAccessor, F)

        val split = path.splitDelta(abstractTree(A, AnyAccessor)).single()
        assertEquals(listOf(A, AnyAccessor), (split.first as AccessPath).access!!.accessorList())
        assertEquals(setOf<Accessor>(F), split.second.getAllAccessors())

        val atAbstract = path.splitDelta(abstractTree(A)).single()
        assertEquals(initial(A), atAbstract.first)
        assertTrue(atAbstract.second.startsWithAccessor(AnyAccessor))

        assertTrue(path.splitDelta(finalTree(A, G, F)).isEmpty())
    }

    /* ---------- splitAny ---------- */

    private fun AccessTree.AccessNode.allPathsCrossAny(): Boolean {
        if (isAbstract || isFinal) return false
        var result = true
        forEachAccessor { accessor, child ->
            if (accessor != with(manager) { AnyAccessor.idx } && !child.allPathsCrossAny()) result = false
        }
        return result
    }

    @Test
    fun `splitAny of a tree without any is the tree itself`() {
        val tree = merged(finalTree(A, F), abstractTree(G))
        val split = tree.access.splitAny()
        assertSame(tree.access, split.complete)
        assertNull(split.any)
    }

    @Test
    fun `splitAny of a pure any tree`() {
        val tree = abstractTree(AnyAccessor, F)
        val split = tree.access.splitAny()
        assertNull(split.complete)
        assertEquals(tree.access, split.any)
    }

    @Test
    fun `splitAny of a mixed tree`() {
        val tree = merged(abstractTree(), finalTree(A, F), abstractTree(A, AnyAccessor, G), finalTree(H, AnyAccessor))
        val split = tree.access.splitAny()

        val complete = assertNotNull(split.complete)
        val any = assertNotNull(split.any)

        assertEquals(merged(abstractTree(), finalTree(A, F)).access, complete)
        assertEquals(merged(abstractTree(A, AnyAccessor, G), finalTree(H, AnyAccessor)).access, any)

        assertFalse(complete.containsAny)
        assertTrue(any.allPathsCrossAny())
        assertEquals(tree.access, complete.mergeAdd(any, foldToAny = false))
    }

    @Test
    fun `splitAny shares the split of a shared subtree`() {
        val shared = abstractTree(F, AnyAccessor, G).access
        val sharedWithComplete = shared.mergeAdd(finalTree(X).access, foldToAny = false)

        val aIdx = with(manager) { A.idx }
        val hIdx = with(manager) { H.idx }
        val yIdx = with(manager) { Y.idx }
        val plain = finalTree(X).access

        val accessors = intArrayOf(aIdx, hIdx, yIdx)
        val order = accessors.indices.sortedBy { accessors[it] }
        val children = arrayOf(sharedWithComplete, sharedWithComplete, plain)

        val root = manager.create(
            isAbstract = false, isFinal = false, deepAccessorExclusion = null,
            accessors = IntArray(3) { accessors[order[it]] },
            accessorNodes = Array(3) { children[order[it]] },
        )

        val split = root.splitAny()
        val complete = assertNotNull(split.complete)
        val any = assertNotNull(split.any)

        assertSame(complete.getChild(aIdx), complete.getChild(hIdx))
        assertSame(any.getChild(aIdx), any.getChild(hIdx))
        assertSame(plain, complete.getChild(yIdx))
        assertNull(any.getChild(yIdx))

        assertFalse(complete.containsAny)
        assertTrue(any.allPathsCrossAny())
        assertEquals(root, complete.mergeAdd(any, foldToAny = false))
    }

    private class TestSerializationContext : SummarySerializationContext {
        private val accessors = mutableListOf<Accessor>()

        override fun getIdByAccessor(accessor: Accessor): Long {
            val idx = accessors.indexOf(accessor)
            if (idx >= 0) return idx.toLong()
            accessors.add(accessor)
            return (accessors.size - 1).toLong()
        }

        override fun getAccessorById(id: Long): Accessor = accessors[id.toInt()]

        override fun getIdByMethod(method: CommonMethod): Long = error("unused")
        override fun getMethodById(id: Long): CommonMethod = error("unused")
        override fun loadSummaries(method: CommonMethod): ByteArray? = error("unused")
        override fun storeSummaries(method: CommonMethod, summaries: ByteArray) = error("unused")
        override fun flush() = Unit
    }
}

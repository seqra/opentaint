package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.NDFactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.SideEffectSummary.FactSideEffectSummary
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.ZeroToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class AnySummaryStorageTest {
    private companion object {
        val A = FieldAccessor("C", "a", "C")
        val F = FieldAccessor("C", "f", "C")
        val G = FieldAccessor("C", "g", "C")
        val H = FieldAccessor("C", "h", "C")
        val K = FieldAccessor("C", "k", "C")
        val MARK = TaintMarkAccessor("m")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private object Kind : SideEffectKind

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val base = AccessPathBase.This
    private val arg = AccessPathBase.LocalVar(0)

    private val exitInst = DummyInst("exit")
    private val entryInst = DummyInst("entry")
    private val entryPoint = MethodEntryPoint(EmptyMethodContext, entryInst)

    private fun initial(
        vararg accessors: Accessor,
        base: AccessPathBase = this.base,
        exclusions: ExclusionSet = ExclusionSet.Empty,
    ): AccessPath =
        accessors.foldRight(manager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }
            .replaceExclusions(exclusions) as AccessPath

    /** this.<accessors>.$ */
    private fun finalTree(vararg accessors: Accessor, exclusions: ExclusionSet = ExclusionSet.Empty): AccessTree =
        accessors.foldRight(manager.createFinalAp(base, exclusions)) { a, f -> f.prependAccessor(a) } as AccessTree

    private fun merged(vararg trees: AccessTree): AccessTree =
        trees.reduce { acc, t -> AccessTree(manager, acc.base, acc.access.mergeAdd(t.access), acc.exclusions) }

    private fun FinalFactAp.node(): AccessTree.AccessNode = (this as AccessTree).access

    private fun AccessTree.AccessNode.allPathsCrossAny(): Boolean {
        if (isAbstract || isFinal) return false
        var result = true
        forEachAccessor { accessor, child ->
            if (accessor != with(manager) { AnyAccessor.idx } && !child.allPathsCrossAny()) result = false
        }
        return result
    }

    /* ---------- nested [any] ---------- */

    @Test
    fun `merging trees with nested any does not crash`() {
        // a.[any].f.[any].g.$ : what a path with two [any]s becomes as a tree
        val nested = merged(finalTree(A, AnyAccessor, F, AnyAccessor, G))
        val other = finalTree(A, AnyAccessor, K)

        val storage = MergingTreeSummaryStorage(manager)
        assertTrue(storage.add(nested.access))
        assertTrue(storage.add(other.access))

        val edges = AccessTree(manager, base, storage.edges()!!, ExclusionSet.Empty)
        assertTrue(edges.contains(finalInitialOf(initial(A, AnyAccessor, F, AnyAccessor, G))))
        assertTrue(edges.contains(finalInitialOf(initial(A, AnyAccessor, K))))

        // the other direction of the merge builds the matcher from the nested side
        val reversed = MergingTreeSummaryStorage(manager)
        assertTrue(reversed.add(other.access))
        assertTrue(reversed.add(nested.access))
        assertEquals(storage.edges(), reversed.edges())
    }

    @Test
    fun `nested any is still trimmed only where it is covered`() {
        // a.[any].f.[any].g.$ covers a.x.f.g.$ (x covered), so the merge may drop it, but it must keep a.m...
        val nested = finalTree(A, AnyAccessor, F, AnyAccessor, G).access
        val covered = finalTree(A, H, F, G).access
        val notCovered = finalTree(A, F, K).access

        val merged = nested.mergeAdd(covered).mergeAdd(notCovered)
        val tree = AccessTree(manager, base, merged, ExclusionSet.Empty)

        assertTrue(tree.contains(finalInitialOf(initial(A, F, K))))
        assertTrue(tree.contains(finalInitialOf(initial(A, AnyAccessor, F, AnyAccessor, G))))
    }

    private fun finalInitialOf(path: AccessPath): AccessPath {
        val accessors = path.access?.accessorList().orEmpty()
        return accessors.foldRight(manager.createFinalInitialAp(base, ExclusionSet.Empty)) { a, f ->
            f.prependAccessor(a)
        } as AccessPath
    }

    /* ---------- F2F ---------- */

    private fun f2fStorage() = MethodInitialToFinalApSummaries(entryInst, manager)

    private fun MethodInitialToFinalApSummaries.add(vararg edges: Pair<InitialFactAp, FinalFactAp>): List<Edge.FactToFact> {
        val added = mutableListOf<FactToFactEdgeBuilder>()
        add(edges.map { (i, f) -> Edge.FactToFact(entryPoint, i, exitInst, f) }, added)
        return added.map { it.setEntryPoint(entryPoint).build() }
    }

    private fun MethodInitialToFinalApSummaries.find(pattern: FinalFactAp?): List<Edge.FactToFact> {
        val dst = mutableListOf<FactToFactEdgeBuilder>()
        filterEdgesTo(dst, pattern, finalFactBase = null)
        return dst.map { it.setEntryPoint(entryPoint).build() }
    }

    @Test
    fun `f2f complete edge stays complete`() {
        val storage = f2fStorage()
        val added = storage.add(initial(A) to finalTree(H, G))

        val edge = added.single()
        assertFalse(edge.factAp.node().containsAny)
        assertEquals(listOf(edge), storage.find(finalTree(A)))
    }

    @Test
    fun `f2f any-only final goes to the any storage`() {
        val storage = f2fStorage()
        val final = finalTree(H, AnyAccessor, G)
        val added = storage.add(initial(A) to final)

        assertEquals(final.node(), added.single().factAp.node())
        assertEquals(added, storage.find(finalTree(A)))
    }

    @Test
    fun `f2f mixed final is split into a complete and an any edge`() {
        val storage = f2fStorage()
        val final = merged(finalTree(H, G), finalTree(H, AnyAccessor, K), finalTree(F))
        val added = storage.add(initial(A) to final)

        assertEquals(2, added.size)
        assertTrue(added.all { it.initialFactAp == initial(A) })

        val (anyEdges, completeEdges) = added.partition { it.factAp.node().containsAny }
        val complete = completeEdges.single().factAp.node()
        val any = anyEdges.single().factAp.node()

        assertEquals(merged(finalTree(H, G), finalTree(F)).access, complete)
        assertTrue(any.allPathsCrossAny())
        assertEquals(final.access, complete.mergeAdd(any, foldToAny = false))

        assertEquals(added.toSet(), storage.find(finalTree(A)).toSet())
    }

    @Test
    fun `f2f initial with any is stored whole and found only by an any pattern`() {
        val storage = f2fStorage()
        val initialAp = initial(A, AnyAccessor, F)
        val final = merged(finalTree(H, G), finalTree(H, AnyAccessor, K))
        val added = storage.add(initialAp to final)

        val edge = added.single()
        assertEquals(initialAp, edge.initialFactAp)
        assertEquals(final.access, edge.factAp.node())

        // [any] is matched exactly: only a caller fact with the [any] edge reaches the key
        assertEquals(listOf(edge), storage.find(finalTree(A, AnyAccessor, F)))
        assertTrue(storage.find(finalTree(A, G, F)).isEmpty())
        assertTrue(storage.find(finalTree(A, F)).isEmpty())
        assertTrue(storage.find(finalTree(H, F)).isEmpty())
        assertEquals(listOf(edge), storage.find(null))
    }

    @Test
    fun `f2f any key at the root is found only by an any pattern`() {
        val storage = f2fStorage()
        val edge = storage.add(initial(AnyAccessor, F) to finalTree(G)).single()
        assertEquals(listOf(edge), storage.find(finalTree(AnyAccessor, F)))
        assertTrue(storage.find(finalTree(H, H, F)).isEmpty())
    }

    @Test
    fun `f2f repeated adds report only the new part`() {
        val storage = f2fStorage()
        val final = merged(finalTree(H, G), finalTree(H, AnyAccessor, K))
        assertEquals(2, storage.add(initial(A) to final).size)

        assertTrue(storage.add(initial(A) to final).isEmpty())

        val newAny = storage.add(initial(A) to finalTree(H, AnyAccessor, MARK)).single()
        assertTrue(newAny.factAp.node().allPathsCrossAny())
        assertFalse(newAny.factAp.contains(finalInitialOf(initial(H, AnyAccessor, K))))

        val newComplete = storage.add(initial(A) to finalTree(F)).single()
        assertEquals(finalTree(F).access, newComplete.factAp.node())

        val anyInitial = initial(A, AnyAccessor, F)
        assertEquals(1, storage.add(anyInitial to finalTree(G)).size)
        assertTrue(storage.add(anyInitial to finalTree(G)).isEmpty())
        assertEquals(finalTree(K).access, storage.add(anyInitial to finalTree(K)).single().factAp.node())
    }

    @Test
    fun `f2f any edges with nested any finals merge`() {
        val storage = f2fStorage()
        assertEquals(1, storage.add(initial(A) to finalTree(A, AnyAccessor, F, AnyAccessor, G)).size)
        assertEquals(1, storage.add(initial(A) to finalTree(A, AnyAccessor, K)).size)
    }

    /* ---------- Z2F ---------- */

    private fun z2fStorage() = MethodFinalTreeApSummariesStorage(entryInst, manager)

    private fun MethodFinalTreeApSummariesStorage.add(vararg finals: FinalFactAp): List<Edge.ZeroToFact> {
        val added = mutableListOf<ZeroToFactEdgeBuilder>()
        add(finals.map { Edge.ZeroToFact(entryPoint, exitInst, it.replaceExclusions(ExclusionSet.Universe)) }, added)
        return added.map { it.setEntryPoint(entryPoint).build() }
    }

    private fun MethodFinalTreeApSummariesStorage.all(): List<Edge.ZeroToFact> {
        val dst = mutableListOf<ZeroToFactEdgeBuilder>()
        filterEdgesTo(dst, finalFactBase = null)
        return dst.map { it.setEntryPoint(entryPoint).build() }
    }

    @Test
    fun `z2f splits finals and reports deltas of both parts`() {
        val storage = z2fStorage()

        assertEquals(1, storage.add(finalTree(F)).size)
        assertTrue(storage.add(finalTree(F)).isEmpty())

        val added = storage.add(merged(finalTree(G), finalTree(H, AnyAccessor, K)))
        assertEquals(2, added.size)
        val (any, complete) = added.partition { it.factAp.node().containsAny }
        assertEquals(finalTree(G).access, complete.single().factAp.node())
        assertTrue(any.single().factAp.node().allPathsCrossAny())

        val onlyAny = storage.add(finalTree(H, AnyAccessor, MARK)).single()
        assertTrue(onlyAny.factAp.node().allPathsCrossAny())

        val all = storage.all()
        assertEquals(2, all.size)
        val (allAny, allComplete) = all.partition { it.factAp.node().containsAny }
        assertEquals(merged(finalTree(F), finalTree(G)).access, allComplete.single().factAp.node())
        assertTrue(allAny.single().factAp.node().allPathsCrossAny())
    }

    /* ---------- NDF2F ---------- */

    private fun ndStorage() = MethodNDInitialToFinalApSummaries(entryInst, manager)

    private fun MethodNDInitialToFinalApSummaries.add(initial: Set<InitialFactAp>, final: FinalFactAp): List<Edge.NDFactToFact> {
        val added = mutableListOf<NDFactToFactEdgeBuilder>()
        val edge = Edge.NDFactToFact(
            entryPoint,
            initial.mapTo(hashSetOf()) { it.replaceExclusions(ExclusionSet.Universe) },
            exitInst,
            final.replaceExclusions(ExclusionSet.Universe),
        )
        add(listOf(edge), added)
        return added.map { it.setEntryPoint(entryPoint).build() }
    }

    private fun MethodNDInitialToFinalApSummaries.find(pattern: FinalFactAp): List<Edge.NDFactToFact> {
        val dst = mutableListOf<NDFactToFactEdgeBuilder>()
        filterEdgesTo(dst, pattern, finalFactBase = null)
        return dst.map { it.setEntryPoint(entryPoint).build() }
    }

    @Test
    fun `ndf2f splits the final of a complete initial set`() {
        val storage = ndStorage()
        val initials = setOf<InitialFactAp>(initial(A), initial(F, base = arg))
        val final = merged(finalTree(G), finalTree(H, AnyAccessor, K))

        val added = storage.add(initials, final)
        assertEquals(2, added.size)
        val (any, complete) = added.partition { it.factAp.node().containsAny }
        assertEquals(finalTree(G).access, complete.single().factAp.node())
        assertTrue(any.single().factAp.node().allPathsCrossAny())

        assertTrue(storage.add(initials, final).isEmpty())
        assertEquals(finalTree(F).access, storage.add(initials, finalTree(F)).single().factAp.node())

        assertEquals(2, storage.find(finalTree(A)).size)
    }

    @Test
    fun `ndf2f initial set with any keeps the final whole`() {
        val storage = ndStorage()
        val initials = setOf<InitialFactAp>(initial(A, AnyAccessor, F), initial(F, base = arg))
        val final = merged(finalTree(G), finalTree(H, AnyAccessor, K))

        val added = storage.add(initials, final).single()
        assertEquals(final.access, added.factAp.node())
        assertTrue(storage.add(initials, final).isEmpty())

        assertEquals(listOf(added), storage.find(finalTree(A, G, F)))
    }

    /* ---------- side effects ---------- */

    @Test
    fun `fact side effect with any initial is found only by an any pattern`() {
        val storage = FactSideEffectSummariesTreeApStorage(entryInst, manager)
        val summary = FactSideEffectSummary(initial(A, AnyAccessor, F), Kind)
        val complete = FactSideEffectSummary(initial(H), Kind)

        val added = mutableListOf<FactSideEffectSummary>()
        storage.add(listOf(summary, complete), added)
        assertEquals(setOf(summary, complete), added.toSet())

        val found = mutableListOf<FactSideEffectSummary>()
        storage.filterTaintedTo(found, finalTree(A, AnyAccessor, F))
        assertEquals(listOf(summary), found)

        val notFound = mutableListOf<FactSideEffectSummary>()
        storage.filterTaintedTo(notFound, finalTree(A, G, F))
        assertTrue(notFound.isEmpty())

        val foundComplete = mutableListOf<FactSideEffectSummary>()
        storage.filterTaintedTo(foundComplete, finalTree(H, G))
        assertEquals(listOf(complete), foundComplete)
    }

    @Test
    fun `side effect requirement with any is found only by an any pattern`() {
        val storage = SideEffectRequirementTreeApStorage(manager)
        val requirement = initial(A, AnyAccessor, F)
        assertEquals(listOf<InitialFactAp>(requirement), storage.add(listOf(requirement)))

        val found = mutableListOf<InitialFactAp>()
        storage.filterTo(found, finalTree(A, AnyAccessor, F))
        assertEquals(listOf<InitialFactAp>(requirement), found)

        val notFound = mutableListOf<InitialFactAp>()
        storage.filterTo(notFound, finalTree(A, G, F))
        assertTrue(notFound.isEmpty())
    }

    private class DummyInst(private val name: String) : CommonInst {
        override fun toString(): String = name
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val index: Int = 0
            override val method: CommonMethod = object : CommonMethod {
                override val name: String = "dummy"
                override val parameters: List<CommonMethodParameter> = emptyList()
                override val returnType: CommonTypeName = object : CommonTypeName {
                    override val typeName: String = "void"
                }

                override fun flowGraph(): ControlFlowGraph<CommonInst> = error("unused")
            }
        }
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonFactEdgeSubBuilder
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
import kotlin.test.assertNotNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

class SummaryRetentionTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val field = FieldAccessor("Owner", "field", "Owner")
    private val nestedField = FieldAccessor("Owner", "nested", "Owner")
    private val otherField = FieldAccessor("Owner", "other", "Owner")
    private val mark = TaintMarkAccessor("summary-retention")

    private fun open(vararg accessors: Accessor): AccessTree.AccessNode {
        var fact: FinalFactAp = manager.mostAbstractFinalAp(AccessPathBase.This)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return (fact as AccessTree).access
    }

    private fun initial(vararg accessors: Accessor): AccessPath {
        var fact: InitialFactAp = manager.mostAbstractInitialAp(AccessPathBase.This)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact as AccessPath
    }

    private fun idx(accessor: Accessor): Int = with(manager) { accessor.idx }

    @Test
    fun `covered sibling absorption reaches an identity fixpoint`() {
        val input = open(AnyAccessor).mergeAdd(open(field, mark))

        val folded = input.absorbCoveredSiblings()

        assertFalse(folded.accessors!!.contains(idx(field)))
        assertTrue(folded.accessors!!.contains(idx(AnyAccessor)))
        assertSame(folded, folded.absorbCoveredSiblings())
    }

    @Test
    fun `a late query reads an absorbed sibling through any`() {
        val folded = open(AnyAccessor).mergeAdd(open(field, mark)).absorbCoveredSiblings()

        val fieldChild = assertNotNull(folded.getChild(idx(field)))

        assertNotNull(fieldChild.getChild(idx(mark)))
    }

    @Test
    fun `absorption normalizes nested any along covered paths`() {
        val input = open(AnyAccessor).mergeAdd(open(field, nestedField, AnyAccessor))

        val folded = input.absorbCoveredSiblings()

        val anyChild = assertNotNull(folded.getChild(idx(AnyAccessor)))
        val pending = ArrayDeque(listOf(anyChild))
        while (pending.isNotEmpty()) {
            val node = pending.removeLast()
            assertFalse(node.containsAnyAccessor())
            node.forEachAccessor { _, child -> pending.addLast(child) }
        }
    }

    @Test
    fun `summary publishes only the normalized retained delta`() {
        val storage = MergingTreeSummaryStorage(manager)
        storage.add(open(AnyAccessor))
        storage.getAndResetDelta()

        assertTrue(storage.add(open(field, mark)))
        val delta = assertNotNull(storage.getAndResetDelta())
        val retained = assertNotNull(storage.edges())

        assertFalse(delta.accessors!!.contains(idx(field)))
        assertTrue(delta.accessors!!.contains(idx(AnyAccessor)))
        assertNotNull(assertNotNull(delta.getChild(idx(AnyAccessor))).getChild(idx(mark)))
        assertFalse(retained.accessors!!.contains(idx(field)))
        assertNotNull(retained.getChild(idx(field)))
    }

    @Test
    fun `tree delta excludes branches already present in retained state`() {
        val retained = open(field)

        val (merged, delta) = retained.mergeAddDelta(open(otherField))

        assertTrue(merged.accessors!!.contains(idx(field)))
        assertTrue(merged.accessors!!.contains(idx(otherField)))
        val published = assertNotNull(delta)
        assertFalse(published.accessors!!.contains(idx(field)))
        assertTrue(published.accessors!!.contains(idx(otherField)))
    }

    @Test
    fun `absorbed edge retention keeps a concrete publication`() {
        val retained = open(AnyAccessor)
        val (merged, delta) = retained.mergeAddDelta(open(field, mark), foldToAny = false)

        val normalized = merged.absorbCoveredSiblings()

        assertFalse(normalized.accessors!!.contains(idx(field)))
        assertNotNull(normalized.getChild(idx(field))?.getChild(idx(mark)))
        val published = assertNotNull(delta)
        assertTrue(published.accessors!!.contains(idx(field)))
        assertFalse(published.accessors!!.contains(idx(AnyAccessor)))
    }

    @Test
    fun `subscription rows factor exclusion variants with the same conclusion`() {
        val storage = SummaryEdgeFactAbstractTreeSubscriptionStorage(manager, dummyInst)
        val initial = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field)
        val first = initial.exclude(nestedField)
        val second = initial.exclude(otherField)

        assertNotNull(storage.add(first, open(field)))
        assertNotNull(storage.add(second, open(field)))

        assertEquals(1, storage.storedRowCount())
    }

    @Test
    fun `subscription rows preserve exclusion correlation across conclusions`() {
        val storage = SummaryEdgeFactAbstractTreeSubscriptionStorage(manager, dummyInst)
        val initial = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field)
        val first = initial.exclude(nestedField)
        val second = initial.exclude(otherField)

        assertNotNull(storage.add(first, open(field)))
        assertNotNull(storage.add(second, open(field, mark)))

        assertEquals(2, storage.storedRowCount())
    }

    @Test
    fun `subscription rows factor conclusions with the same exclusions`() {
        val storage = SummaryEdgeFactAbstractTreeSubscriptionStorage(manager, dummyInst)
        val initial = manager.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(field).exclude(nestedField)

        assertNotNull(storage.add(initial, open(field)))
        assertNotNull(storage.add(initial, open(field, mark)))

        assertEquals(1, storage.storedRowCount())
    }

    @Test
    fun `flat path index preserves root and promoted entries`() {
        val interner = AccessPathInterner(manager, dummyInst)
        val created = mutableListOf<Int>()
        val rootIndex = interner.getOrCreateIndex(AccessPathBase.This, null, created::add)
        val fieldAccess = initial(field).access
        val fieldIndex = interner.getOrCreateIndex(AccessPathBase.This, fieldAccess, created::add)
        val nestedAccess = initial(field, nestedField).access
        val nestedIndex = interner.getOrCreateIndex(AccessPathBase.This, nestedAccess, created::add)

        assertEquals(rootIndex, interner.getOrCreateIndex(AccessPathBase.This, null, created::add))
        assertEquals(fieldIndex, interner.getOrCreateIndex(AccessPathBase.This, fieldAccess, created::add))
        assertEquals(nestedIndex, interner.getOrCreateIndex(AccessPathBase.This, nestedAccess, created::add))
        assertEquals(listOf(0, 1, 2), created)
        assertEquals(listOf(0, 1, 2), interner.findBaseIndices(AccessPathBase.This)!!.stream().toArray().toList())
    }

    @Test
    fun `empty delta lookup excludes a nonabstract remainder`() {
        val storage = SummaryEdgeFactAbstractTreeSubscriptionStorage(manager, dummyInst)
        storage.add(initial(nestedField), open(field))
        storage.add(initial(otherField), open(field, mark))
        val result = mutableListOf<CommonFactEdgeSubBuilder<AccessTree.AccessNode>>()

        storage.find(result, initial(field).access, emptyDeltaRequired = true)

        assertEquals(1, result.size)
    }

    @Test
    fun `root empty delta lookup excludes a nonabstract root`() {
        val storage = SummaryEdgeFactAbstractTreeSubscriptionStorage(manager, dummyInst)
        storage.add(initial(nestedField), open())
        storage.add(initial(otherField), open(field))
        val result = mutableListOf<CommonFactEdgeSubBuilder<AccessTree.AccessNode>>()

        storage.find(result, summaryInitialFact = null, emptyDeltaRequired = true)

        assertEquals(1, result.size)
    }

    private val dummyInst = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val index: Int = 0
            override val method: CommonMethod = object : CommonMethod {
                override val name: String = "dummy"
                override val parameters: List<CommonMethodParameter> = emptyList()
                override val returnType: CommonTypeName = object : CommonTypeName {
                    override val typeName: String = "void"
                }

                override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
                    override val instructions: List<CommonInst> = emptyList()
                    override val entries: List<CommonInst> = emptyList()
                    override val exits: List<CommonInst> = emptyList()
                    override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
                    override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
                }
            }
        }
    }
}

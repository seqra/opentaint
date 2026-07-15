package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyFactSetTest {
    private val mark = TaintMarkAccessor("m")
    private val field1 = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")

    private fun mkManager(fieldSensitive: Boolean = false) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = fieldSensitive)

    private val dummyMethod = object : CommonMethod {
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

    private val inst = object : CommonInst {
        override fun toString(): String = "i0"
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = dummyMethod
        }
    }

    private val lm = object : LanguageManager {
        override fun getInstIndex(inst: CommonInst): Int = 0
        override fun getMaxInstIndex(method: CommonMethod): Int = 0
        override fun getInstByIndex(method: CommonMethod, index: Int): CommonInst = error("unused")
        override fun isEmpty(method: CommonMethod): Boolean = error("unused")
        override fun getCallExpr(inst: CommonInst): CommonCallExpr? = null
        override fun producesExceptionalControlFlow(inst: CommonInst): Boolean = false
        override fun getCalleeMethod(callExpr: CommonCallExpr): CommonMethod = error("unused")
        override val methodContextSerializer: MethodContextSerializer get() = error("unused")
    }

    private fun BaseOnlyApManager.finalFact(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var fact = createFinalAp(base, ExclusionSet.Universe)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    @Test
    fun `z2f dedups any covered field variants via normalization`() {
        val m = mkManager()
        val set = m.methodEdgesFinalApSet(inst, 0, lm)

        val anyMark = m.finalFact(AccessPathBase.This, AnyAccessor, mark)
        val added1 = set.add(inst, anyMark)
        assertNotNull(added1, "first add returns a fact")
        assertTrue(added1.startsWithAccessor(field1), "returned fact is any-expanded (field insensitive)")

        val bareMark = m.finalFact(AccessPathBase.This, mark)
        assertNull(set.add(inst, bareMark), "bare mark subsumed by stored normalized mark")

        val collected = mutableListOf<FinalFactAp>()
        set.collectApAtStatement(collected, inst)
        assertEquals(1, collected.size, "single normalized entry stored")
    }

    @Test
    fun `z2f expands bare mark on add`() {
        val m = mkManager()
        val set = m.methodEdgesFinalApSet(inst, 0, lm)
        val added = set.add(inst, m.finalFact(AccessPathBase.This, mark))
        assertNotNull(added)
        assertTrue(added.startsWithAccessor(field1), "bare mark is expanded to any-covering form on enqueue")
    }

    @Test
    fun `z2f keeps distinct fields when field extension enabled`() {
        val m = mkManager(fieldSensitive = true)
        val set = m.methodEdgesFinalApSet(inst, 0, lm)
        assertNotNull(set.add(inst, m.finalFact(AccessPathBase.This, field1, mark)))
        assertNotNull(set.add(inst, m.finalFact(AccessPathBase.This, field2, mark)), "distinct field kept under extension")
    }

    @Test
    fun `f2f dedups and returns on new edge`() {
        val m = mkManager()
        val set = m.methodEdgesInitialToFinalApSet(inst, 0, lm)
        val initial = m.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(ExclusionSet.Empty)
        val final = m.createFinalAp(AccessPathBase.This, ExclusionSet.Empty).prependAccessor(mark)

        assertNotNull(set.add(inst, initial, final), "first f2f edge is new")
        assertNull(set.add(inst, initial, final), "same f2f edge subsumed")

        val collected = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        set.collectApAtStatement(collected, inst)
        assertEquals(1, collected.size)
    }

    @Test
    fun `nd f2f dedups`() {
        val m = mkManager()
        val set = m.methodEdgesNDInitialToFinalApSet(inst, 0, lm)
        val i1 = m.mostAbstractInitialAp(AccessPathBase.This).prependAccessor(mark)
        val i2 = m.mostAbstractInitialAp(AccessPathBase.Return).prependAccessor(mark)
        val initial = setOf(i1, i2)
        val final = m.finalFact(AccessPathBase.ClassStatic, mark)

        assertNotNull(set.add(inst, initial, final))
        assertNull(set.add(inst, initial, final))
    }
}

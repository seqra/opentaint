package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
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

class BaseOnlySummaryNormalizationTest {
    @Test
    fun `field initial is moved to suffix when summary final has suffix`() {
        val static = 41
        val field = 73
        val initial = packBaseOnlyAccess(static, ABSTRACT_MARK, NO_ACCESSOR)
        val final = packBaseOnlyAccess(static, field, ABSTRACT_MARK)

        val normalized = normalizeSummaryInitialAccess(initial, final)

        assertEquals(packBaseOnlyAccess(static, NO_ACCESSOR, ABSTRACT_MARK), normalized)
    }

    @Test
    fun `field initial is unchanged when summary final has field abstraction`() {
        val initial = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)
        val final = packBaseOnlyAccess(NO_ACCESSOR, ABSTRACT_MARK, NO_ACCESSOR)

        assertEquals(initial, normalizeSummaryInitialAccess(initial, final))
    }

    @Test
    fun `suffix initial is unchanged`() {
        val initial = packBaseOnlyAccess(NO_ACCESSOR, NO_ACCESSOR, ABSTRACT_MARK)
        val final = packBaseOnlyAccess(NO_ACCESSOR, 73, ABSTRACT_MARK)

        assertEquals(initial, normalizeSummaryInitialAccess(initial, final))
    }

    @Test
    fun `normalized aliases are queryable but do not report deltas`() {
        val manager = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)
        val storage = MethodInitialToFinalBaseOnlyApSummariesStorage(inst, manager)
        val static = 41
        val field = 73
        val initialAccess = packBaseOnlyAccess(static, ABSTRACT_MARK, NO_ACCESSOR)
        val normalizedAccess = packBaseOnlyAccess(static, NO_ACCESSOR, ABSTRACT_MARK)
        val finalAccess = packBaseOnlyAccess(static, field, ABSTRACT_MARK)
        val edge = Edge.FactToFact(
            entryPoint,
            BaseOnlyInitialFactAp(manager, AccessPathBase.Argument(0), initialAccess, ExclusionSet.Empty),
            inst,
            BaseOnlyFinalFactAp(manager, AccessPathBase.Return, finalAccess, ExclusionSet.Empty),
        )

        val added = mutableListOf<FactToFactEdgeBuilder>()
        storage.add(listOf(edge), added)

        assertEquals(1, added.size, "the normalized alias must not be reported as a new summary delta")
        assertEquals(initialAccess, added.single().buildForTest().initialAccess)
        assertFalse(normalizedAccess in storage.initialAccesses(), "normalized aliases stay hidden until trace resolution")

        manager.enableNormalizedEdges()

        val queried = storage.initialAccesses()
        assertTrue(initialAccess in queried, "the original summary remains queryable")
        assertTrue(normalizedAccess in queried, "the normalized alias remains available to trace resolution")
    }

    private fun MethodInitialToFinalBaseOnlyApSummariesStorage.initialAccesses(): Set<BaseOnlyAccess> {
        val result = mutableListOf<FactToFactEdgeBuilder>()
        filterEdgesTo(result, initialFactPattern = null, finalFactBase = AccessPathBase.Return)
        return result.mapTo(hashSetOf()) { it.buildForTest().initialAccess }
    }

    private fun FactToFactEdgeBuilder.buildForTest(): BuiltEdge =
        setEntryPoint(entryPoint).build().let {
            BuiltEdge((it.initialFactAp as BaseOnlyInitialFactAp).access)
        }

    private data class BuiltEdge(val initialAccess: BaseOnlyAccess)

    private val method: CommonMethod = object : CommonMethod {
        override val name: String = "summaryNormalization"
        override val parameters: List<CommonMethodParameter> = listOf(object : CommonMethodParameter {
            override val type: CommonTypeName = object : CommonTypeName {
                override val typeName: String = "java.lang.Object"
            }
        })
        override val returnType: CommonTypeName = object : CommonTypeName {
            override val typeName: String = "java.lang.Object"
        }

        override fun flowGraph(): ControlFlowGraph<CommonInst> = object : ControlFlowGraph<CommonInst> {
            override val instructions: List<CommonInst> = emptyList()
            override val entries: List<CommonInst> = emptyList()
            override val exits: List<CommonInst> = emptyList()
            override fun successors(node: CommonInst): Set<CommonInst> = emptySet()
            override fun predecessors(node: CommonInst): Set<CommonInst> = emptySet()
        }
    }

    private val inst: CommonInst = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod get() = this@BaseOnlySummaryNormalizationTest.method
        }
    }

    private val entryPoint = MethodEntryPoint(EmptyMethodContext, inst)
}

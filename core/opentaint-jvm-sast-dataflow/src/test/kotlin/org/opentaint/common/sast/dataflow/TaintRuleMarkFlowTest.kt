package org.opentaint.common.sast.dataflow

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.Argument
import org.opentaint.dataflow.configuration.jvm.AssignMark
import org.opentaint.dataflow.configuration.jvm.ContainsMark
import org.opentaint.dataflow.configuration.jvm.Result
import org.opentaint.dataflow.configuration.jvm.TaintMark
import org.opentaint.dataflow.configuration.jvm.TaintMethodSource
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class TaintRuleMarkFlowTest {
    @Test
    fun `extracts condition and assigned marks`() {
        val input = TaintMark("input")
        val output = TaintMark("output")
        val action = AssignMark(output, Result)
        val rule = TaintMethodSource(
            method = TestMethod,
            condition = CommonCondition.Atom(ContainsMark(Argument(0), input)),
            actionsAfter = listOf(action),
            info = null,
        )

        val flow = rule.taintRuleMarkFlow(setOf(action))

        assertEquals(setOf("input"), flow.inputMarks)
        assertEquals(setOf("output"), flow.outputMarks)
        assertTrue(flow.outputMarksComplete)
    }

    private data object TestMethod : CommonMethod {
        override val name: String = "test"
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

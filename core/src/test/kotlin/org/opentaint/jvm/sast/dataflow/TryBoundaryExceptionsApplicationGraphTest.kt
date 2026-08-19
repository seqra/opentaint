package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.opentaint.ir.api.jvm.cfg.JIRCatchInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.impl.features.usagesExt
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.sast.ast.BasicTestUtils

class TryBoundaryExceptionsApplicationGraphTest : BasicTestUtils() {
    override val sourceFileExtension: String = "java"

    @Test
    fun `explicit throws and the last try statement are connected to catch handlers`() {
        val method = findMethod(
            "test.samples.ExplicitExceptionEdgesSample",
            "caughtExplicitThrow",
        )
        val catch = method.instList.filterIsInstance<JIRCatchInst>().single()
        val explicitThrow = method.instList.filterIsInstance<JIRThrowInst>().single()
        val implicitThrowingCall = method.instList.single {
            it.callExpr?.method?.method?.name == "implicitThrower"
        }
        val lastTryStatement = method.instList.single {
            it.callExpr?.method?.method?.name == "lastTryStatement"
        }

        val usages = runBlocking { cp.usagesExt() }
        val baseGraph = JApplicationGraphImpl(cp, usages)
        val graph = JTryBoundaryExceptionsApplicationGraph(baseGraph).methodGraph(method)
        val selectedExceptionSources = graph.predecessors(catch).toSet()

        assertTrue(catch in graph.successors(explicitThrow).toSet())
        assertTrue(explicitThrow in graph.predecessors(catch).toSet())
        assertTrue(catch in graph.successors(lastTryStatement).toSet())
        assertTrue(lastTryStatement in graph.predecessors(catch).toSet())
        assertFalse(catch in graph.successors(implicitThrowingCall).toSet())
        assertFalse(implicitThrowingCall in graph.predecessors(catch).toSet())
        assertEquals(setOf(explicitThrow, lastTryStatement), selectedExceptionSources)
    }
}

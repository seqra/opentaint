package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.cactus.CactusApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.serialization.MethodContextSerializer
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.CommonMethodParameter
import org.opentaint.ir.api.common.CommonTypeName
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonInstLocation
import org.opentaint.ir.api.common.cfg.ControlFlowGraph
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class MethodEdgesInitialToFinalApSetTest {
    private val method = object : CommonMethod {
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

    private val statement = object : CommonInst {
        override val location: CommonInstLocation = object : CommonInstLocation {
            override val method: CommonMethod = this@MethodEdgesInitialToFinalApSetTest.method; override val index: Int = 0 }
    }

    private val languageManager = object : LanguageManager {
        override fun getInstIndex(inst: CommonInst): Int = 0
        override fun getMaxInstIndex(method: CommonMethod): Int = 0
        override fun getInstByIndex(method: CommonMethod, index: Int): CommonInst = statement
        override fun isEmpty(method: CommonMethod): Boolean = false
        override fun getCallExpr(inst: CommonInst): CommonCallExpr? = null
        override fun producesExceptionalControlFlow(inst: CommonInst): Boolean = false
        override fun getCalleeMethod(callExpr: CommonCallExpr): CommonMethod = error("unused")
        override val methodContextSerializer: MethodContextSerializer get() = error("unused")
    }

    @Test
    fun `exclusion changes publish the complete final language for every AP implementation`() {
        val strategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled
        val managers = listOf(
            "Tree" to TreeApManager(strategy, RefManager(), org.opentaint.dataflow.util.Cancellation()),
            "Automata" to AutomataApManager(strategy, org.opentaint.dataflow.util.Cancellation()),
            "Cactus" to CactusApManager(strategy, org.opentaint.dataflow.util.Cancellation()),
            "BaseOnly" to BaseOnlyApManager(strategy, org.opentaint.dataflow.util.Cancellation(), fieldSensitive = true),
        )

        managers.forEach { (name, manager) ->
            val exclusion1 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-1"))
            val exclusion2 = ExclusionSet.Concrete(TaintMarkAccessor("excluded-2"))
            val mergedExclusion = exclusion1.union(exclusion2)
            val initial1 = manager.mostAbstractInitialAp(AccessPathBase.Return).replaceExclusions(exclusion1)
            val initial2 = initial1.replaceExclusions(exclusion2)
            val final1 = manager.createFinalAp(AccessPathBase.This, exclusion1)
                .prependAccessor(TaintMarkAccessor("mark-1"))
            val final2 = manager.createFinalAp(AccessPathBase.This, exclusion2)
                .prependAccessor(TaintMarkAccessor("mark-2"))
            val edges = manager.methodEdgesInitialToFinalApSet(statement, 0, languageManager)

            assertEquals(1, edges.add(statement, initial1, final1).size, "$name first delta")
            val delta = edges.add(statement, initial2, final2)
            val stored = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
            edges.collectApAtStatement(stored, statement)

            assertEquals(stored.toSet(), delta.toSet(), "$name must re-emit its complete stored language")
            assertTrue(delta.all { it.first.exclusions == mergedExclusion }, "$name initial exclusions")
            assertTrue(delta.all { it.second.exclusions == mergedExclusion }, "$name final exclusions")
            assertTrue(edges.add(statement, initial2, final2).isEmpty(), "$name duplicate delta")
        }
    }

    @Test
    fun `batch insertion has the same exact delta as scalar insertion`() {
        val strategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled
        val managers = listOf(
            "Tree" to TreeApManager(strategy, RefManager(), org.opentaint.dataflow.util.Cancellation()),
            "Automata" to AutomataApManager(strategy, org.opentaint.dataflow.util.Cancellation()),
            "Cactus" to CactusApManager(strategy, org.opentaint.dataflow.util.Cancellation()),
            "BaseOnly" to BaseOnlyApManager(strategy, org.opentaint.dataflow.util.Cancellation(), fieldSensitive = true),
        )

        managers.forEach { (name, manager) ->
            val exclusion = ExclusionSet.Concrete(TaintMarkAccessor("excluded"))
            val initials = listOf(
                manager.mostAbstractInitialAp(AccessPathBase.This)
                    .prependAccessor(TaintMarkAccessor("origin-1"))
                    .replaceExclusions(exclusion),
                manager.mostAbstractInitialAp(AccessPathBase.LocalVar(0))
                    .prependAccessor(TaintMarkAccessor("origin-2"))
                    .replaceExclusions(exclusion),
            )
            val final = manager.createFinalAp(AccessPathBase.Return, exclusion)
                .prependAccessor(TaintMarkAccessor("result"))
            val scalar = manager.methodEdgesInitialToFinalApSet(statement, 0, languageManager)
            val batch = manager.methodEdgesInitialToFinalApSet(statement, 0, languageManager)

            val scalarDelta = initials.flatMap { scalar.add(statement, it, final) }
            val batchDelta = arrayListOf<Pair<InitialFactAp, FinalFactAp>>()
            batch.addAll(statement, initials, final) { initial, addedFinal ->
                batchDelta += initial to addedFinal
            }

            assertEquals(scalarDelta, batchDelta, "$name propagation delta")

            val scalarState = arrayListOf<Pair<InitialFactAp, FinalFactAp>>()
            val batchState = arrayListOf<Pair<InitialFactAp, FinalFactAp>>()
            scalar.collectApAtStatement(scalarState, statement)
            batch.collectApAtStatement(batchState, statement)
            assertEquals(scalarState.toSet(), batchState.toSet(), "$name stored relation")
        }
    }
}

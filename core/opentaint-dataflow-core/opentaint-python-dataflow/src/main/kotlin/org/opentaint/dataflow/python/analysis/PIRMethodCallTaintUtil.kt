package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.configuration.python.ContainsMark
import org.opentaint.dataflow.configuration.python.PIRCondition
import org.opentaint.dataflow.configuration.python.TaintConfigurationSource
import org.opentaint.dataflow.configuration.python.TaintSink
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.resolveAp
import org.opentaint.dataflow.python.adapter.PIRCallExprAdapter
import org.opentaint.dataflow.taint.FactReader
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.FinalFactReaderWithPrefix
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.dataflow.taint.TaintUtil
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.util.onSome

class PIRMethodCallTaintUtil(
    val context: PIRMethodAnalysisContext,
    val statement: PIRInstruction,
    val callExpr: PIRCallExprAdapter,
    apManager: ApManager
) : TaintUtil<ContainsMark, TaintConfigurationSource, TaintSink, TraceInfo>(apManager) {
    val callFactMapper get() = context.methodCallFactMapper

    override fun TaintConfigurationSource.srcCondition(): PIRCondition = condition

    override fun TaintSink.sinkCondition() = condition

    override fun sourceAssumptionsManager(): RuleAssumptionsManager<TaintConfigurationSource> =
        object : RuleAssumptionsManager<TaintConfigurationSource> {
            override fun storeAssumptions(
                rule: TaintConfigurationSource,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                TODO("Not yet implemented")
            }

            override fun currentAssumptions(rule: TaintConfigurationSource): Set<InitialFactAp> {
                TODO("Not yet implemented")
            }
        }

    override fun sinkAssumptionsManager(): RuleAssumptionsManager<TaintSink> =
        object : RuleAssumptionsManager<TaintSink> {
            override fun storeAssumptions(
                rule: TaintSink,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                TODO("Not yet implemented")
            }

            override fun currentAssumptions(rule: TaintSink): Set<InitialFactAp> {
                TODO("Not yet implemented")
            }
        }

    override fun conditionFact(factReader: FinalFactReader): List<FinalFactReader> = buildList {
        callFactMapper.mapMethodCallToStartFlowFact(
            statement,
            callee = statement.location.method,
            callExpr,
            returnValue = null,
            factReader.factAp,
            FactTypeChecker.Dummy,
        ) { fact, startBase ->
            this += FinalFactReader(fact.rebase(startBase), apManager)
        }
    }

    override fun handleReachedSink(
        rule: TaintSink,
        factReader: FinalFactReader?,
        evaluatedFacts: List<InitialFactAp>
    ) {
        val callerFacts = evaluatedFacts.mapTo(hashSetOf()) {
            callFactMapper.mapMethodExitToReturnFlowFact(statement, it).single()
        }

        context.taint.taintSinkTracker.addVulnerability(
            context.methodEntryPoint,
            callerFacts,
            statement,
            rule
        )
    }

    override fun applySourceAction(
        rule: TaintConfigurationSource,
        sourceEvaluator: TaintSourceActionEvaluator,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit
    ) {
        rule.taint.forEach { action ->
            val pos = action.pos.resolveAp() ?: return@forEach
            val mark = TaintMarkAccessor(action.mark.name)
            sourceEvaluator.evaluate(rule, action, pos, mark).onSome { facts ->
                facts.forEach { fact ->
                    val callerFacts = callFactMapper.mapMethodExitToReturnFlowFact(statement, fact, FactTypeChecker.Dummy)
                    callerFacts.forEach { createFinalFact(it, TraceInfo.Flow) }
                }
            }
        }
    }

    override fun patchSinkConditionFactReader(factReaders: List<FinalFactReader>): List<FactReader> {
        val arrayElementFactReaders = factReaders.arrayElementConditionReaders()
        return factReaders + arrayElementFactReaders
    }

    private fun List<FinalFactReader>.arrayElementConditionReaders(): List<FactReader> =
        mapNotNull {
            val base = it.factAp.base as? AccessPathBase.Argument ?: return@mapNotNull null

            val arrayElementPosition = PositionAccess.Complex(PositionAccess.Simple(base), ElementAccessor)
            if (!it.containsPosition(arrayElementPosition)) return@mapNotNull null

            FinalFactReaderWithPrefix(it, ElementAccessor)
        }
}

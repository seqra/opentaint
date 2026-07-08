package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.python.PIRCondition
import org.opentaint.dataflow.configuration.python.PythonRuleCondition
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
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.util.onSome
import kotlin.collections.plusAssign

abstract class PIRTaintUtil<I : PIRInstruction, TraceInfo>(
    val context: PIRMethodAnalysisContext,
    val statement: I,
    apManager: ApManager
) : TaintUtil<PythonRuleCondition, TaintConfigurationSource, TaintSink, TraceInfo>(apManager) {
    private val sinkTracker get() = context.taint.taintSinkTracker

    override fun TaintConfigurationSource.srcCondition(): PIRCondition = condition

    override fun TaintSink.sinkCondition() = condition

    override fun sourceAssumptionsManager(): RuleAssumptionsManager<TaintConfigurationSource> =
        object : RuleAssumptionsManager<TaintConfigurationSource> {
            override fun storeAssumptions(
                rule: TaintConfigurationSource,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                sinkTracker.addSourceRuleAssumptions(rule, statement, assumptions)
            }

            override fun currentAssumptions(rule: TaintConfigurationSource): Set<InitialFactAp> =
                sinkTracker.currentSourceRuleAssumptions(rule, statement)

            override fun currentAssumptionPreconditions(
                rule: TaintConfigurationSource,
                assumptions: List<InitialFactAp>
            ) = sinkTracker.currentSourceRuleAssumptionsPreconditions(rule, statement, assumptions)
        }

    override fun sinkAssumptionsManager(): RuleAssumptionsManager<TaintSink> =
        object : RuleAssumptionsManager<TaintSink> {
            override fun storeAssumptions(
                rule: TaintSink,
                assumptions: Map<InitialFactAp, Set<InitialFactAp>>
            ) {
                sinkTracker.addSinkRuleAssumptions(rule, statement, assumptions)
            }

            override fun currentAssumptions(rule: TaintSink): Set<InitialFactAp> =
                sinkTracker.currentSinkRuleAssumptions(rule, statement)
        }

    override fun handleReachedSink(
        rule: TaintSink,
        factReader: FinalFactReader?,
        evaluatedFacts: List<InitialFactAp>
    ) {
        val callerFacts = evaluatedFacts.mapTo(hashSetOf()) {
            mapFactToReturn(it).single()
        }

        context.taint.taintSinkTracker.addVulnerability(
            context.methodEntryPoint,
            callerFacts,
            statement,
            rule
        )
    }

    /** The call to resolve `kwarg(name)` positions against; null for attribute loads (no kwargs). */
    protected open val positionCall: PIRCall? get() = null

    override fun applySourceAction(
        rule: TaintConfigurationSource,
        sourceEvaluator: TaintSourceActionEvaluator,
        createFinalFact: (FinalFactAp, TraceInfo) -> Unit
    ) {
        rule.taint.forEach { action ->
            val pos = action.pos.resolveAp(positionCall) ?: return@forEach
            val trace = createRuleTraceInfo(rule, action)
            val mark = TaintMarkAccessor(action.mark.name)
            sourceEvaluator.evaluate(rule, action, pos, mark).onSome { facts ->
                facts.forEach { fact ->
                    val callerFacts = mapFactToReturn(fact)
                    callerFacts.forEach { createFinalFact(it, trace) }
                }
            }
        }
    }

    abstract fun createRuleTraceInfo(rule: CommonTaintConfigurationItem, action: CommonTaintAction): TraceInfo
    abstract fun mapFactToReturn(fact: FinalFactAp): List<FinalFactAp>
    abstract fun mapFactToReturn(fact: InitialFactAp): List<InitialFactAp>
}

class PIRMethodCallTaintUtil(
    val callExpr: PIRCallExprAdapter,
    context: PIRMethodAnalysisContext,
    statement: PIRCall,
    apManager: ApManager
) : PIRTaintUtil<PIRCall, TraceInfo>(context, statement, apManager) {
    private val callFactMapper get() = context.methodCallFactMapper

    override fun createRuleTraceInfo(rule: CommonTaintConfigurationItem, action: CommonTaintAction): TraceInfo =
        TraceInfo.Rule(rule, action)

    override val positionCall get() = statement

    override fun mapFactToReturn(fact: FinalFactAp) =
        callFactMapper.mapMethodExitToReturnFlowFact(statement, fact, FactTypeChecker.Dummy)

    override fun mapFactToReturn(fact: InitialFactAp) =
        callFactMapper.mapMethodExitToReturnFlowFact(statement, fact)

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
}

class PIRAttributeLoadTaintUtil(
    context: PIRMethodAnalysisContext,
    statement: PIRLoadAttr,
    apManager: ApManager,
) : PIRTaintUtil<PIRLoadAttr, MethodSequentFlowFunction.TraceInfo>(context, statement, apManager) {
    private val callFactMapper get() = context.methodCallFactMapper

    override fun createRuleTraceInfo(rule: CommonTaintConfigurationItem, action: CommonTaintAction) =
        MethodSequentFlowFunction.TraceInfo.Rule(rule, action)

    override fun mapFactToReturn(fact: FinalFactAp) =
        listOfNotNull(callFactMapper.mapLoadAttributeFactToReturn(statement, fact))

    override fun mapFactToReturn(fact: InitialFactAp) = TODO()

    override fun conditionFact(factReader: FinalFactReader): List<FinalFactReader> = buildList {
        callFactMapper.mapLoadAttributeFactToStart(statement, factReader.factAp) { fact, newBase ->
            this += FinalFactReader(fact.rebase(newBase), apManager)
        }
    }
}

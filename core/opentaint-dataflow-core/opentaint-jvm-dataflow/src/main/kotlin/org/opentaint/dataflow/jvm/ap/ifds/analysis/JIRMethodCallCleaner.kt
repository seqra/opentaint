package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.serialized.UserDefinedRuleInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodPositionBaseTypeResolver
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.applyCleaner
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRTaintCleanActionEvaluator
import org.opentaint.dataflow.jvm.util.callee
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.TaintFactAwareConditionEvaluator
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst

class JIRMethodCallCleaner(
    private val apManager: ApManager,
    private val analysisContext: JIRMethodAnalysisContext,
    private val returnValue: JIRImmediate?,
    private val callExpr: JIRCallExpr,
    private val statement: JIRInst,
) {
    fun interface CleanerInputs {
        fun inputs(
            calleeFact: FinalFactAp,
            cleanRules: List<RuleWithCondition<TaintCleaner>>,
            conditionEvaluator: TaintFactAwareConditionEvaluator,
        ): List<FinalFactAp>
    }

    private val typeResolver by lazy {
        JIRMethodPositionBaseTypeResolver(callExpr.method.method)
    }

    fun applyCleanersOrCallToStart(
        originalFactReader: FinalFactReader,
        unmappedCallerFactAp: FinalFactAp,
        startFactBase: AccessPathBase,
        addCallToReturn: (FinalFactReader, FinalFactAp, TraceInfo) -> Unit,
        addCallToStart: (factReader: FinalFactReader, callerFactAp: FinalFactAp, startFactBase: AccessPathBase, TraceInfo) -> Unit,
        addUnchecked: (MethodCallFlowFunction.CallFact) -> Unit,
        cleanerInputs: CleanerInputs = CleanerInputs { calleeFact, _, _ -> listOf(calleeFact) },
    ) {
        val calleeFact = unmappedCallerFactAp.rebase(startFactBase)
        applyCleaners(
            originalFactReader, calleeFact, cleanerInputs,
            onDrop = { trace -> addUnchecked(MethodCallFlowFunction.Drop(trace)) }
        ) { factReaderAfterCleaner ->
            val cleanedFact = factReaderAfterCleaner.factAp
            check(cleanedFact.base == startFactBase)

            val unmappedFact = cleanedFact.rebase(unmappedCallerFactAp.base)

            if (callExpr.callee.isConstructor) {
                addCallToReturn(originalFactReader, unmappedFact, TraceInfo.Flow)
            }

            addCallToStart(originalFactReader, unmappedFact, startFactBase, TraceInfo.Flow)
        }
    }

    fun applyCleaners(
        refinementReader: FinalFactReader,
        calleeFact: FinalFactAp,
        cleanerInputs: CleanerInputs,
        onDrop: (TraceInfo?) -> Unit,
        onCleaned: (FinalFactReader) -> Unit,
    ) {
        val conditionFactReader = FinalFactReader(calleeFact, apManager)

        val conditionEvaluator = TaintFactAwareConditionEvaluator(
            listOf(conditionFactReader),
            markAfterAnyAccessorResolver = null
        )

        val cleaner = JIRTaintCleanActionEvaluator(typeResolver)

        val cleanRules = analysisContext.taint.cleanRulesForCallStatement(statement, callExpr, returnValue, calleeFact)
        val cleanerResults = cleanerInputs.inputs(calleeFact, cleanRules, conditionEvaluator).flatMap { fact ->
            applyCleaner(cleanRules, FinalFactReader(fact, apManager), conditionEvaluator, cleaner)
        }

        refinementReader.updateRefinement(conditionFactReader)

        for (cleanerResult in cleanerResults) {
            val factReaderAfterCleaner = cleanerResult.fact
            if (factReaderAfterCleaner == null) {
                val trace = cleanerResult.action
                    ?.takeIf { (it.rule as? TaintConfigurationItem)?.info is UserDefinedRuleInfo }
                    ?.let { TraceInfo.Rule(it.rule, it.action) }
                onDrop(trace)
                continue
            }

            refinementReader.updateRefinement(factReaderAfterCleaner)
            onCleaned(factReaderAfterCleaner)
        }
    }
}

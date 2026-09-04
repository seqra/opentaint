package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.CombinedMethodContext
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodStartFlowFunction.StartFact
import org.opentaint.dataflow.jvm.ap.ifds.JIRArgumentTypeMethodContext
import org.opentaint.dataflow.jvm.ap.ifds.JIRInstanceTypeMethodContext
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.applyEntryPointConfig
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.toType
import org.opentaint.util.onSome

class JIRMethodStartFlowFunction(
    private val apManager: ApManager,
    private val context: JIRMethodAnalysisContext,
) : MethodStartFlowFunction {
    override fun propagateZero(): List<StartFact> {
        val result = mutableListOf<StartFact>()
        result.add(StartFact.Zero)

        applySinkRules().mapTo(result) { StartFact.Fact(it) }

        val sourceEvaluator = TaintSourceActionEvaluator(
            apManager,
            exclusion = ExclusionSet.Universe
        )

        val rules = context.taint.sourceRulesForMethodEntry(context.methodEntryPoint.statement as JIRInst, fact = null)
        applyEntryPointConfig(rules, sourceEvaluator) { rule, action ->
            context.recordForwardSourceAction(context.methodEntryPoint.statement, rule, action)
        }.onSome { facts ->
            facts.mapTo(result) {
                it.getAllAccessors()
                    .filterIsInstanceTo<TaintMarkAccessor, _>(context.taintMarksAssignedOnMethodEnter)

                StartFact.Fact(it)
            }
        }

        return result
    }

    override fun propagateFact(fact: FinalFactAp): List<StartFact.Fact> {
        val checkedFact = checkInitialFactTypes(context.methodEntryPoint, fact) ?: return emptyList()
        return listOf(StartFact.Fact(checkedFact))
    }

    private fun checkInitialFactTypes(methodEntryPoint: MethodEntryPoint, factAp: FinalFactAp): FinalFactAp? {
        val locationClass = methodEntryPoint.context.locationClass(methodEntryPoint, factAp.base)
        val locationType = locationClass?.toType()
        return context.factTypeChecker.filterFactByLocalType(locationType, factAp)
    }

    private fun MethodContext.locationClass(
        methodEntryPoint: MethodEntryPoint,
        base: AccessPathBase
    ): JIRClassOrInterface? = when (this) {
        is EmptyMethodContext -> if (base is AccessPathBase.This) {
            (methodEntryPoint.method as? JIRMethod)?.enclosingClass
        } else null

        is JIRInstanceTypeMethodContext -> if (base is AccessPathBase.This) {
            typeConstraint.type
        } else null

        is JIRArgumentTypeMethodContext -> if (base is AccessPathBase.Argument && base.idx == argIdx) {
            typeConstraint.type
        } else null

        is CombinedMethodContext -> first.locationClass(methodEntryPoint, base)
            ?: second.locationClass(methodEntryPoint, base)

        else -> error("Unexpected value for context: $context")
    }

    private fun applySinkRules(): List<FinalFactAp> {
        val statement = context.methodEntryPoint.statement

        val sinkRules = context.taint.sinkRulesForMethodEntry(statement as JIRInst, fact = null).toList()
        if (sinkRules.isEmpty()) return emptyList()

        val sourceEvaluator = TaintSourceActionEvaluator(
            apManager,
            exclusion = ExclusionSet.Universe
        )

        val factsAfterSink = mutableListOf<FinalFactAp>()
        for (ruleWithCondition in sinkRules) {
            if (!ruleWithCondition.condition.isTrue) {
                continue
            }

            val rule = ruleWithCondition.rule
            if (rule.trackFactsReachAnalysisEnd.isEmpty()) {
                context.taint.taintSinkTracker.addUnconditionalVulnerability(
                    context.methodEntryPoint, statement, rule
                )
                continue
            }

            val requiredEndFacts = hashSetOf<FinalFactAp>()
            rule.trackFactsReachAnalysisEnd.forEach { action ->
                sourceEvaluator.accept(rule, action).onSome { facts ->
                    facts.forEach { f ->
                        requiredEndFacts += f
                        factsAfterSink += f
                    }
                }
            }

            context.taint.taintSinkTracker.addUnconditionalVulnerabilityWithEndFactRequirement(
                context.methodEntryPoint, statement, rule, requiredEndFacts
            )
        }

        return factsAfterSink
    }
}

package org.opentaint.dataflow.jvm.ap.ifds.trace

import mu.KLogging
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.TaintConfigUtils.accept
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRStatementSummary
import org.opentaint.dataflow.jvm.ap.ifds.taint.resolveAp
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.dataflow.taint.evaluateSourceRulePrecondition
import org.opentaint.dataflow.taint.preconditionDnf
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.jvm.graph.JMethodExitExceptionalInst
import org.opentaint.jvm.graph.JMethodExitNormalInst
import org.opentaint.util.maybeFlatMap

class JIRMethodSequentPrecondition(
    private val apManager: ApManager,
    private val currentInst: JIRInst,
    private val analysisContext: JIRMethodAnalysisContext,
) : MethodSequentPrecondition {
    private val summary: StatementSummary by lazy {
        JIRStatementSummary.buildReversed(apManager, currentInst, analysisContext.aliasAnalysis)
    }

    override fun factPrecondition(
        fact: InitialFactAp,
    ): Set<SequentPrecondition> = when (currentInst) {
        is JMethodExitNormalInst, is JMethodExitExceptionalInst -> methodExitPrecondition(fact)

        is JIRAssignInst, is JIRReturnInst, is JIRThrowInst -> {
            val results = mutableSetOf<SequentPrecondition>()
            results.computeFactPrecondition(fact)
            results
        }

        else -> setOf(SequentPrecondition.Unchanged)
    }

    private fun methodExitPrecondition(fact: InitialFactAp): Set<SequentPrecondition> {
        val results = mutableSetOf<SequentPrecondition>(SequentPrecondition.Unchanged)
        results.methodExitSourcePrecondition(fact)
        return results
    }

    private fun MutableSet<SequentPrecondition>.computeFactPrecondition(fact: InitialFactAp) {
        val precondition = preconditionForFact(fact).toMutableSet()

        precondition.unconditionalSourcesPrecondition(fact)
        this += precondition.ifEmpty { setOf(SequentPrecondition.Unchanged) }
    }

    private fun preconditionForFact(fact: InitialFactAp): Set<SequentPrecondition> = when (currentInst) {
        is JMethodExitNormalInst, is JMethodExitExceptionalInst -> setOf(PreconditionFactsForInitialFact(fact, listOf(fact)))

        is JIRAssignInst, is JIRReturnInst, is JIRThrowInst -> summary.sequentPreconditions(fact)

        else -> emptySet()
    }

    private fun MutableSet<SequentPrecondition>.unconditionalSourcesPrecondition(fact: InitialFactAp) {
        if (currentInst !is JIRAssignInst) return

        val rhvFieldRef = currentInst.rhv as? JIRFieldRef ?: return
        val field = rhvFieldRef.field.field
        if (!field.isStatic) return

        val lhv = accessPathBase(currentInst.lhv) ?: return
        if (fact.base != lhv) return

        val config = analysisContext.taint
        val sourceRules = config.sourceRulesForStaticField(field, currentInst, fact = null).toList()
        if (sourceRules.isEmpty()) return

        val entryFactReader = InitialFactReader(fact.rebase(AccessPathBase.Return), apManager)
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(entryFactReader)

        for (sourceRuleWithCond in sourceRules) {
            if (!sourceRuleWithCond.condition.isTrue) continue

            val sourceRule = sourceRuleWithCond.rule
            val assignedMarks = sourceRule.actionsAfter.maybeFlatMap {
                sourcePreconditionEvaluator.accept(sourceRule, it)
            }
            if (assignedMarks.isNone) continue

            val sourceActions = assignedMarks.getOrThrow().mapTo(hashSetOf()) { it.second }

            this += MethodSequentPrecondition.SequentSource(
                fact, TaintRulePrecondition.Source(sourceRule, sourceActions)
            )
        }
    }

    private fun MutableSet<SequentPrecondition>.methodExitSourcePrecondition(fact: InitialFactAp) {
        val config = analysisContext.taint
        val sourceRules = config.sourceRulesForMethodExit(currentInst, fact = null).toList()
        if (sourceRules.isEmpty()) return

        val entryFactReader = InitialFactReader(fact, apManager)
        val sourcePreconditionEvaluator = TaintSourceActionPreconditionEvaluator(entryFactReader)

        for (ruleWithCond in sourceRules) {
            evaluateSourceRulePrecondition(
                ruleWithCond, ruleWithCond.rule.actionsAfter, sourcePreconditionEvaluator,
                evalAction = { r, a -> evaluate(r, a, a.position.resolveAp(), TaintMarkAccessor(a.mark.name)) },
                mkSource = { r, a ->
                    val src = TaintRulePrecondition.Source(r, a)
                    this += MethodSequentPrecondition.SequentSource(fact, src)
                },
                mkPass = { _, _, e ->
                    val preconditionFacts = e.preconditionDnf(
                        apManager,
                        allFactsAtStatement = { TODO("All facts enumeration is not supported") }
                    ) { listOf(it) }
                    for (factCube in preconditionFacts) {
                        if (factCube.facts.size != 1) {
                            logger.warn("Exit source precondition is not resolved")
                            continue
                        }

                        val preFact = factCube.facts.single()
                        computeFactPrecondition(preFact)
                    }
                }
            )
        }
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}

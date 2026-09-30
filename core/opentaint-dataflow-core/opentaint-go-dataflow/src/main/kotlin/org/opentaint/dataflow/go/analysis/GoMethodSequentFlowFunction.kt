package org.opentaint.dataflow.go.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary
import org.opentaint.dataflow.go.analysis.GoMethodCallResolver.ClosureCreationFlowFunction
import org.opentaint.dataflow.taint.TaintSourceActionEvaluator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.inst.GoIRInst

class GoMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val context: GoMethodAnalysisContext,
    private val currentInst: GoIRInst,
    private val generateTrace: Boolean,
) : MethodSequentFlowFunction {

    private val method: GoIRFunction get() = context.method

    private val summary: StatementSummary by lazy {
        GoStatementSummary.build(apManager, currentInst, method, context.aliasAnalysis)
    }

    override fun propagateZeroToZero(): Set<Sequent> {
        val zeroSequents = mutableSetOf<Sequent>(Sequent.ZeroToZero)
        applyGlobalOrFieldReadSourceRules(zeroSequents)

        ClosureCreationFlowFunction.handle(context, currentInst) { base, accessors ->
            val startFact = apManager.createFinalAp(base, ExclusionSet.Universe)
            val fact = accessors.foldRight(startFact) { a, f -> f.prependAccessor(a) }
            zeroSequents += Sequent.ZeroToFact(fact, traceInfoOrNull())
        }

        return zeroSequents
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp) = buildSet {
        propagate(
            factAp = currentFactAp,
            propagateFact = { fact ->
                check(fact.exclusions is ExclusionSet.Universe) {
                    "Zero to Fact edge can't be refined: $currentFactAp"
                }
                add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
            },
            refineInitial = { },
        )
    }

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp) = buildSet {
        propagate(
            factAp = currentFactAp,
            propagateFact = { fact ->
                if (fact.exclusions is ExclusionSet.Universe) {
                    add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
                } else {
                    val refinedInitial = initialFactAp.replaceExclusions(fact.exclusions)
                    add(Sequent.FactToFact(refinedInitial, fact, TraceInfo.Flow))
                    if (refinedInitial != initialFactAp) {
                        add(Sequent.SideEffectRequirement(refinedInitial))
                    }
                }
            },
            refineInitial = { exclusions ->
                val refinedInitial = initialFactAp.replaceExclusions(exclusions)
                if (refinedInitial != initialFactAp) {
                    add(Sequent.SideEffectRequirement(refinedInitial))
                }
            },
        )
    }

    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp) = buildSet {
        propagate(
            factAp = currentFactAp,
            propagateFact = { fact ->
                check(fact.exclusions is ExclusionSet.Universe) {
                    "NDF2F edge can't be refined: $currentFactAp"
                }
                add(Sequent.NDFactToFact(initialFacts, fact, TraceInfo.Flow))
            },
            refineInitial = { },
        )
    }

    private fun MutableSet<Sequent>.propagate(
        factAp: FinalFactAp,
        propagateFact: (FinalFactAp) -> Unit,
        refineInitial: (ExclusionSet) -> Unit,
    ) {
        val typeChecker = context.analysisManager.factTypeChecker
        if (!summary.transfer(factAp, typeChecker, propagateFact, refineInitial)) {
            add(Sequent.Unchanged)
        }
    }

    private fun applyGlobalOrFieldReadSourceRules(out: MutableSet<Sequent>) {
        applyGlobalOrFieldReadSourceRules(
            currentInst, context,
            mkSourceEvaluator = { TaintSourceActionEvaluator(apManager, ExclusionSet.Universe) }
        ) { rule, action, lhv, fact ->
            val trace = TraceInfo.Rule(rule, action)
            if (fact.base !is AccessPathBase.Return) {
                TODO("Field/global source with non-result assign")
            }
            out += Sequent.ZeroToFact(fact.rebase(lhv), trace)
        }
    }

    private fun traceInfoOrNull(): TraceInfo? = if (generateTrace) TraceInfo.Flow else null
}

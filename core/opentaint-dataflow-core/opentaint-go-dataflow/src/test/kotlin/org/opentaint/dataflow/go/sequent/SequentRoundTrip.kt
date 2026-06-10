package org.opentaint.dataflow.go.sequent

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisUnitStorage
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.dataflow.go.analysis.GoMethodSequentFlowFunction
import org.opentaint.dataflow.go.analysis.alias.GoLocalAliasAnalysis
import org.opentaint.dataflow.go.rules.GoTaintAnalysisContext
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.go.trace.GoMethodSequentPrecondition
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.inst.GoIRInst

data class FactSpec(val base: AccessPathBase, val accessors: List<Accessor>) {
    fun append(tail: List<Accessor>): FactSpec = if (tail.isEmpty()) this else FactSpec(base, accessors + tail)

    override fun toString(): String =
        base.toString() + accessors.joinToString("") { it.toSuffix() }
}

data class Scenario(
    val label: String,
    val inst: GoIRInst,
    val before: FactSpec,
    val afters: List<FactSpec>,
    val roundTrip: Boolean,
    val exact: Boolean,
)

class SequentFixture(program: GoIRProgram, val fn: GoIRFunction) {
    val apManager: ApManager = TreeApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled)

    private val context: GoMethodAnalysisContext = run {
        val taintConfig = GoTaintConfiguration()
        val manager = GoAnalysisManager(program, taintConfig)
        val storage = TaintAnalysisUnitStorage(apManager, manager)
        val sinkTracker = TaintSinkTracker(storage)
        val taintCtx = GoTaintAnalysisContext(sinkTracker, taintConfig, null)
        val aliasAnalysis = GoLocalAliasAnalysis(fn)
        val entry = MethodEntryPoint(EmptyMethodContext, fn.body!!.instructions.first() as CommonInst)
        GoMethodAnalysisContext(entry, taintCtx, aliasAnalysis)
    }

    val method: GoIRFunction get() = context.method

    fun ff(inst: GoIRInst) = GoMethodSequentFlowFunction(apManager, context, inst, false)
    fun pre(inst: GoIRInst) = GoMethodSequentPrecondition(apManager, inst, context)

    fun FactSpec.initial(): InitialFactAp =
        accessors.foldRight(apManager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }

    fun FactSpec.final(exclusions: ExclusionSet = ExclusionSet.Empty): FinalFactAp =
        accessors.foldRight(apManager.createFinalAp(base, exclusions)) { a, f -> f.prependAccessor(a) }

    private fun Set<Sequent>.producedFacts(): Set<FinalFactAp> = mapNotNullTo(hashSetOf()) {
        when (it) {
            is Sequent.FactToFact -> it.factAp
            is Sequent.ZeroToFact -> it.factAp
            else -> null
        }
    }

    fun checkForwardF2F(s: Scenario) {
        val produced = ff(s.inst).propagateFactToFact(s.before.initial(), s.before.final()).producedFacts()
        val expected = s.afters.mapTo(hashSetOf()) { it.final() }
        if (s.exact) {
            require(produced == expected) { "F2F ${s.label}: produced $produced, expected $expected" }
        } else {
            require(produced.containsAll(expected)) { "F2F ${s.label}: produced $produced, missing from $expected" }
        }
    }

    fun checkForwardZ2F(s: Scenario) {
        val produced = ff(s.inst).propagateZeroToFact(s.before.final()).producedFacts()
        val expected = s.afters.mapTo(hashSetOf()) { it.final() }
        if (s.exact) {
            require(produced == expected) { "Z2F ${s.label}: produced $produced, expected $expected" }
        } else {
            require(produced.containsAll(expected)) { "Z2F ${s.label}: produced $produced, missing from $expected" }
        }
    }

    fun checkForwardThenPrecondition(s: Scenario) {
        val beforeInitial = s.before.initial()
        for (after in s.afters) {
            val preconditions = pre(s.inst).factPrecondition(after.initial())
            require(preconditions != setOf<SequentPrecondition>(SequentPrecondition.Unchanged)) {
                "precondition ${s.label} for $after must not be only Unchanged, got $preconditions"
            }
            val preFacts = preconditions.filterIsInstance<PreconditionFactsForInitialFact>().flatMap { it.preconditionFacts }
            require(beforeInitial in preFacts) {
                "precondition ${s.label} for $after must yield $beforeInitial, got $preconditions"
            }
        }
    }

    fun checkBackwardThenForward(s: Scenario) {
        val beforeInitial = s.before.initial()
        for (after in s.afters) {
            val preFacts = pre(s.inst).factPrecondition(after.initial())
                .filterIsInstance<PreconditionFactsForInitialFact>().flatMap { it.preconditionFacts }
            require(beforeInitial in preFacts) {
                "backward ${s.label} for $after must yield $beforeInitial, got $preFacts"
            }
            val produced = ff(s.inst).propagateFactToFact(s.before.initial(), s.before.final()).producedFacts()
            require(after.final() in produced) {
                "backward->forward ${s.label} must reproduce ${after.final()}, got $produced"
            }
        }
    }
}

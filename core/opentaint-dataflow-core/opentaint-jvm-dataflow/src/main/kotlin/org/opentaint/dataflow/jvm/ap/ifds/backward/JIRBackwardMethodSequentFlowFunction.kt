package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.jvm.Condition
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.MemoryAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.RefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.StaticRefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.writeToAccessor
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodAnalysisContext
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction.FactRefiner
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction.SequentEmitter
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardTaintAnalysisContext.Companion.positiveMarks
import org.opentaint.dataflow.jvm.ap.ifds.taint.JIRSequentTaintUtil
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.jvm.graph.JMethodEnterInst

class JIRBackwardMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRMethodAnalysisContext,
    private val taint: JIRBackwardTaintAnalysisContext,
    private val currentInst: JIRInst,
) : MethodSequentFlowFunction {
    private val forward = JIRMethodSequentFlowFunction(apManager, analysisContext, currentInst, generateTrace = false)

    override fun propagateZeroToFact(currentFactAp: FinalFactAp) = buildSet<Sequent> {
        propagate(emptySet(), currentFactAp, SequentEmitter.zeroToFact(this, currentFactAp))
    }

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp) = buildSet<Sequent> {
        propagate(setOf(initialFactAp), currentFactAp, SequentEmitter.factToFact(this, initialFactAp, currentFactAp))
    }

    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp) = buildSet<Sequent> {
        propagate(initialFacts, currentFactAp, SequentEmitter.ndFactToFact(this, initialFacts, currentFactAp))
    }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        when (currentInst) {
            is JIRReturnInst -> {
                for ((fact, _) in forward.applyMethodExitSourceRules(AccessPathBase.Return, fact = null, refiner = null)) {
                    val zeroFact: (FinalFactAp) -> Unit = { add(Sequent.ZeroToFact(it, TraceInfo.Flow)) }
                    moveDemand(AccessPathBase.Return, returnValue(currentInst), fact, zeroFact, zeroFact)
                }
                applyUnconditionalExitSinks(AccessPathBase.Return)
            }

            is JIRThrowInst -> applyUnconditionalExitSinks(AccessPathBase.Exception)

            is JMethodEnterInst -> {
                sinkUtil<TaintMethodEntrySink>(AccessPathBase.Return)
                    .applySinkRules(entrySinkRules(currentInst), factReader = null, markAfterAnyFieldResolver = null)
                applySourceRules(entrySourceRules(currentInst), AccessPathBase.Return, fact = null, refiner = null)
                    .forEach { add(Sequent.ZeroToFact(it, TraceInfo.Flow)) }
            }
        }
    }

    private fun propagate(
        initialFacts: Set<InitialFactAp>,
        factAp: FinalFactAp,
        emitter: SequentEmitter,
    ) {
        val refiner = FactRefiner()
        val demands = mutableListOf<FinalFactAp>()

        when (currentInst) {
            is JIRAssignInst -> {
                applyStaticFieldRules(currentInst, factAp, refiner, demands)
                val exclude = { fact: FinalFactAp, accessor: Accessor ->
                    emitter.propagateFactWithAccessorExclude(fact, accessor, TraceInfo.Flow)
                }

                if (!refiner.hasRefinement && demands.isEmpty()) {
                    assign(currentInst, factAp, emitter::unchanged, { emitter.propagateFact(it, TraceInfo.Flow) }, exclude)
                } else {
                    assign(currentInst, factAp, { demands += factAp }, demands::add, exclude)
                }
            }

            is JIRReturnInst -> {
                forward.applyMethodExitSinkRules(AccessPathBase.Return, factAp, initialFacts, emitter::sideEffect, refiner)
                val facts = listOf(factAp) + forward.applyMethodExitSourceRules(AccessPathBase.Return, factAp, refiner).map { it.first }
                facts.forEach { moveDemand(AccessPathBase.Return, returnValue(currentInst), it, demands::add, demands::add) }
            }

            is JIRThrowInst -> {
                val throwable = accessPathBase(currentInst.throwable)
                moveDemand(AccessPathBase.Exception, throwable, factAp, demands::add, demands::add)
            }

            is JMethodEnterInst -> {
                val sinks = entrySinkRules(currentInst)
                val sources = entrySourceRules(currentInst)
                val conditions = sinks.map { it.rule.condition } + sources.map { it.rule.condition }
                if (!leavesThroughArgumentRoot(conditions, initialFacts)) {
                    val util = sinkUtil<TaintMethodEntrySink>(AccessPathBase.Return)
                    util.applySinkRules(sinks, FinalFactReader(factAp, apManager), markAfterAnyFieldResolver = null)
                    util.conditionReaders.forEach(refiner::add)
                    demands += applySourceRules(sources, AccessPathBase.Return, factAp, refiner)
                }

                demands += factAp
            }

            else -> emitter.unchanged()
        }

        for (demand in demands) {
            if (demand == factAp && !refiner.hasRefinement) {
                emitter.unchanged()
            } else {
                emitter.propagateFactWithRefinement(refiner, demand, TraceInfo.Flow)
            }
        }
    }

    private fun applyUnconditionalExitSinks(methodResult: AccessPathBase) {
        val rules = taint.sinkRulesForMethodExit(currentInst, fact = null, initialFacts = emptySet())
        sinkUtil<TaintMethodExitSink>(methodResult).applySinkRules(rules, factReader = null, markAfterAnyFieldResolver = null)
    }

    private fun returnValue(inst: JIRReturnInst): AccessPathBase? = inst.returnValue?.let { accessPathBase(it) }

    private fun <Sink : TaintConfigurationSink> sinkUtil(methodResult: AccessPathBase) =
        JIRSequentTaintUtil<TaintConfigurationSource, Sink>(
            apManager, currentInst, analysisContext, generateTrace = false, methodResult
        )

    private fun entrySinkRules(inst: JIRInst): List<RuleWithCondition<TaintMethodEntrySink>> =
        taint.sinkRulesForMethodEntry(inst, fact = null)

    private fun entrySourceRules(inst: JIRInst): List<RuleWithCondition<TaintEntryPointSource>> =
        taint.sourceRulesForMethodEntry(inst, fact = null)

    private fun <Source : TaintConfigurationSource> applySourceRules(
        rules: List<RuleWithCondition<Source>>,
        methodResult: AccessPathBase,
        fact: FinalFactAp?,
        refiner: FactRefiner?,
    ): List<FinalFactAp> {
        if (rules.isEmpty()) return emptyList()

        val result = mutableListOf<FinalFactAp>()
        val util = JIRSequentTaintUtil<Source, TaintConfigurationSink>(
            apManager, currentInst, analysisContext, generateTrace = false, methodResult
        )
        util.applySourceRules(
            rules,
            initialFacts = emptySet(),
            factReader = fact?.let { FinalFactReader(it, apManager) },
            exclusion = fact?.exclusions ?: ExclusionSet.Universe,
            createFinalFact = { f, _ -> result += f },
            createEdge = { _, _, _ -> error("Unused operation") },
            createNDEdge = { _, _, _ -> error("Unused operation") }
        )
        refiner?.let { util.conditionReaders.forEach(it::add) }
        return result
    }

    private fun applyStaticFieldRules(
        inst: JIRAssignInst,
        fact: FinalFactAp,
        refiner: FactRefiner,
        demands: MutableList<FinalFactAp>,
    ) {
        val field = (inst.rhv as? JIRFieldRef)?.field?.field?.takeIf { it.isStatic } ?: return
        val lhv = accessPathBase(inst.lhv) ?: return
        if (fact.base != lhv) return

        val sinks = taint.sinkRulesForStaticField(field, inst)
        val sources = taint.sourceRulesForStaticField(field, inst, fact = null)
        if (sinks.isEmpty() && sources.isEmpty()) return

        val util = sinkUtil<TaintMethodSink>(lhv)
        util.applySinkRules(sinks, FinalFactReader(fact, apManager), markAfterAnyFieldResolver = null)
        util.conditionReaders.forEach(refiner::add)

        demands += applySourceRules(sources, lhv, fact, refiner)
    }

    private fun leavesThroughArgumentRoot(
        conditions: List<Condition>,
        initialFacts: Set<InitialFactAp>,
    ): Boolean {
        if (initialFacts.isEmpty()) return false

        val marks = conditions.flatMapTo(hashSetOf()) { condition ->
            condition.positiveMarks().map { TaintMarkAccessor(it.mark.name) }
        }
        return initialFacts.all { initialFact ->
            val base = initialFact.base
            (base is AccessPathBase.Argument || base is AccessPathBase.This) &&
                marks.any { initialFact.startsWithAccessor(it) }
        }
    }

    private fun assign(
        inst: JIRAssignInst,
        factAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit,
    ) = forward.forEachAssignOperands(inst.rhv, inst.lhv, factAp) { assignFrom, assignTo, fact ->
        val onUnchanged: (FinalFactAp) -> Unit = if (fact != factAp) propagateFact else { _ -> unchanged() }

        when {
            assignFrom is MemoryAccess -> readDemand(assignTo.base, assignFrom, fact, onUnchanged, propagateFact)
            assignTo is MemoryAccess -> writeDemand(
                assignTo, assignFrom?.base, fact, onUnchanged, propagateFact, propagateFactWithAccessorExclude
            )
            else -> moveDemand(assignTo.base, assignFrom?.base, fact, onUnchanged, propagateFact)
        }
    }

    private fun moveDemand(
        assignTo: AccessPathBase,
        assignFrom: AccessPathBase?,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        if (assignTo != factAp.base || assignTo == assignFrom) return unchanged(factAp)
        if (assignFrom != null && assignFrom !is AccessPathBase.Constant) propagateFact(factAp.rebase(assignFrom))
    }

    private fun readDemand(
        assignTo: AccessPathBase,
        access: MemoryAccess,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        if (factAp.base != assignTo) return unchanged(factAp)
        forward.moveIntoField(access, factAp, propagateFact)
    }

    private fun writeDemand(
        access: MemoryAccess,
        assignFrom: AccessPathBase?,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit
    ) {
        when (access) {
            is RefAccess -> forward.clearWrittenField(access, factAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            is StaticRefAccess -> clearStaticField(access, factAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
        }

        val value = assignFrom?.takeUnless { it is AccessPathBase.Constant } ?: return
        val readValue = { fact: FinalFactAp, exclude: (FinalFactAp, Accessor) -> Unit ->
            forward.fieldRead(value, access, fact, {}, { if (it.base == value) propagateFact(it) }, exclude)
        }

        readValue(factAp, propagateFactWithAccessorExclude)

        if (access !is RefAccess || factAp.base == access.base) return
        forEachWriteAlias(access, factAp, propagateFactWithAccessorExclude) { aliased ->
            readValue(aliased) { _, accessor -> propagateFactWithAccessorExclude(factAp, accessor) }
        }
    }

    private fun clearStaticField(
        access: StaticRefAccess,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit
    ) {
        val classAccess = RefAccess(access.base, access.classStaticAccessor)
        forward.clearWrittenField(classAccess, factAp, unchanged, propagateFact, propagateFactWithAccessorExclude)

        val classFields = AccessPathBase.LocalVar.create(-1)
        val restore = { fields: FinalFactAp ->
            val restored = fields.writeToAccessor(access.base, access.classStaticAccessor)
            if (restored == factAp) unchanged(restored) else propagateFact(restored)
        }

        forward.fieldRead(classFields, classAccess, factAp, {}, { fields ->
            if (fields.base == classFields) {
                forward.clearWrittenField(RefAccess(classFields, access.accessor), fields, restore, restore) { _, accessor ->
                    propagateFactWithAccessorExclude(factAp, accessor)
                }
            }
        }, { _, _ -> })
    }

    private inline fun forEachWriteAlias(
        access: RefAccess,
        factAp: FinalFactAp,
        exclude: (FinalFactAp, Accessor) -> Unit,
        body: (FinalFactAp) -> Unit,
    ) {
        val instance = access.base as? AccessPathBase.LocalVar ?: return
        val aliases = analysisContext.aliasAnalysis?.findAlias(instance, currentInst) ?: return

        for (alias in aliases) {
            if (alias !is AliasApInfo || alias.base != factAp.base) continue

            var aliased: FinalFactAp? = factAp
            for (aliasAccessor in alias.accessors) {
                val current = aliased ?: break
                val accessor = aliasAccessor.apAccessor()
                if (current.isAbstract() && accessor !in current.exclusions) exclude(factAp, accessor)
                aliased = current.readAccessor(accessor)
            }

            aliased?.let { body(it.rebase(instance)) }
        }
    }
}

package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FilterResult
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodEntrySink
import org.opentaint.dataflow.configuration.jvm.TaintMethodSink
import org.opentaint.dataflow.jvm.ap.ifds.CalleePositionToJIRValueResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRMarkAwareConditionRewriter
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.MemoryAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.RefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.StaticRefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.writeToAccessor
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardTaintRulesProvider.Companion.isShadowMark
import org.opentaint.dataflow.jvm.ap.ifds.backward.JIRBackwardTaintRulesProvider.Companion.markPositions
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
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val currentInst: JIRInst,
) : JIRMethodSequentFlowFunction(apManager, analysisContext, currentInst, generateTrace = false) {
    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        when (currentInst) {
            is JIRReturnInst -> for ((fact, _) in applyMethodExitSourceRules(AccessPathBase.Return, fact = null, refiner = null)) {
                val zeroFact: (FinalFactAp) -> Unit = { add(Sequent.ZeroToFact(it, TraceInfo.Flow)) }
                simpleAssign(AccessPathBase.Return, returnValue(currentInst), fact, zeroFact, zeroFact)
            }

            is JMethodEnterInst -> sinkUtil<TaintMethodEntrySink>(AccessPathBase.Return)
                .applySinkRules(entrySinkRules(currentInst), factReader = null, markAfterAnyFieldResolver = null)
        }
    }

    override fun propagate(
        initialFacts: Set<InitialFactAp>?,
        factAp: FinalFactAp,
        unchanged: () -> Unit,
        propagateFact: (FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithRefinement: (FactRefiner, FinalFactAp, TraceInfo) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor, TraceInfo) -> Unit,
        sideEffect: (Sequent.SideEffect) -> Unit
    ) {
        val refiner = FactRefiner()
        val demands = mutableListOf<FinalFactAp>()

        when (currentInst) {
            is JIRAssignInst -> {
                applyStaticFieldSinks(currentInst, factAp, refiner)
                if (!refiner.hasRefinement) return super.propagate(
                    initialFacts, factAp, unchanged, propagateFact,
                    propagateFactWithRefinement, propagateFactWithAccessorExclude, sideEffect
                )

                super.propagate(
                    initialFacts, factAp, { demands += factAp }, { fact, _ -> demands += fact },
                    propagateFactWithRefinement, propagateFactWithAccessorExclude, sideEffect
                )
            }

            is JIRReturnInst -> {
                applyMethodExitSinkRules(AccessPathBase.Return, factAp, initialFacts, sideEffect, refiner)
                val facts = listOf(factAp) + applyMethodExitSourceRules(AccessPathBase.Return, factAp, refiner).map { it.first }
                facts.forEach { simpleAssign(AccessPathBase.Return, returnValue(currentInst), it, demands::add, demands::add) }
            }

            is JIRThrowInst -> {
                val throwable = accessPathBase(currentInst.throwable)
                simpleAssign(AccessPathBase.Exception, throwable, factAp, demands::add, demands::add)
            }

            is JMethodEnterInst -> {
                val rules = entrySinkRules(currentInst)
                if (!leavesThroughArgumentRoot(rules, initialFacts.orEmpty())) {
                    val util = sinkUtil<TaintMethodEntrySink>(AccessPathBase.Return)
                    util.applySinkRules(rules, FinalFactReader(factAp, apManager), markAfterAnyFieldResolver = null)
                    util.conditionReaders.forEach(refiner::add)
                }

                keptAtMethodEnter(initialFacts.orEmpty(), factAp)?.let(demands::add)
            }

            else -> unchanged()
        }

        for (demand in demands) {
            if (demand == factAp && !refiner.hasRefinement) {
                unchanged()
            } else {
                propagateFactWithRefinement(refiner, demand, TraceInfo.Flow)
            }
        }
    }

    private fun returnValue(inst: JIRReturnInst): AccessPathBase? = inst.returnValue?.let { accessPathBase(it) }

    private fun <Sink : TaintConfigurationSink> sinkUtil(methodResult: AccessPathBase) =
        JIRSequentTaintUtil<TaintConfigurationSource, Sink>(
            apManager, currentInst, analysisContext, generateTrace = false, methodResult
        )

    private fun entrySinkRules(inst: JIRInst): List<RuleWithCondition<TaintMethodEntrySink>> =
        analysisContext.taint.sinkRulesForMethodEntry(inst, fact = null)

    private fun applyStaticFieldSinks(inst: JIRAssignInst, fact: FinalFactAp, refiner: FactRefiner) {
        val field = (inst.rhv as? JIRFieldRef)?.field?.field?.takeIf { it.isStatic } ?: return
        val lhv = accessPathBase(inst.lhv) ?: return
        if (fact.base != lhv) return

        val sinks = analysisContext.rules.sinkRulesForStaticField(field, inst)
        if (sinks.isEmpty()) return

        val rewriter = JIRMarkAwareConditionRewriter(
            CalleePositionToJIRValueResolver(inst.location.method), analysisContext, inst
        )
        val rules = sinks.map { RuleWithCondition(it, rewriter.rewrite(it.condition)) }

        val util = sinkUtil<TaintMethodSink>(lhv)
        util.applySinkRules(rules, FinalFactReader(fact, apManager), markAfterAnyFieldResolver = null)
        util.conditionReaders.forEach(refiner::add)
    }

    private fun leavesThroughArgumentRoot(
        rules: List<RuleWithCondition<TaintMethodEntrySink>>,
        initialFacts: Set<InitialFactAp>,
    ): Boolean {
        if (initialFacts.isEmpty()) return false

        val marks = rules.flatMapTo(hashSetOf()) { rule ->
            rule.rule.condition.markPositions().map { TaintMarkAccessor(it.mark.name) }
        }
        return initialFacts.all { initialFact ->
            val base = initialFact.base
            (base is AccessPathBase.Argument || base is AccessPathBase.This) &&
                marks.any { initialFact.startsWithAccessor(it) }
        }
    }

    private fun keptAtMethodEnter(initialFacts: Set<InitialFactAp>, fact: FinalFactAp): FinalFactAp? {
        if (!fact.getAllAccessors().any(::isShadowMarkAccessor)) return fact
        if (initialFacts.any { it.isAbstract() || it.getAllAccessors().any(::isShadowMarkAccessor) }) return fact
        return fact.filterFact(ShadowMarkRemover)
    }

    private fun isShadowMarkAccessor(accessor: Accessor): Boolean = accessor is TaintMarkAccessor && isShadowMark(accessor)

    private object ShadowMarkRemover : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FilterResult = when {
            accessor !is TaintMarkAccessor -> FilterResult.FilterNext(this)
            isShadowMark(accessor) -> FilterResult.Reject
            else -> FilterResult.Accept
        }
    }

    override fun simpleAssign(
        assignTo: AccessPathBase,
        assignFrom: AccessPathBase?,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
    ) {
        if (assignTo != factAp.base || assignTo == assignFrom) return unchanged(factAp)
        if (assignFrom != null && assignFrom !is AccessPathBase.Constant) propagateFact(factAp.rebase(assignFrom))
    }

    override fun fieldRead(
        assignTo: AccessPathBase,
        access: MemoryAccess,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit
    ) {
        if (factAp.base != assignTo) return unchanged(factAp)

        val value = AccessPathBase.LocalVar.create(-1)
        super.fieldWrite(access, value, factAp.rebase(value), {}, propagateFact, propagateFactWithAccessorExclude)
    }

    override fun fieldWrite(
        access: MemoryAccess,
        assignFrom: AccessPathBase?,
        factAp: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagateFact: (FinalFactAp) -> Unit,
        propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit
    ) {
        when (access) {
            is RefAccess -> super.fieldWrite(access, null, factAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
            is StaticRefAccess -> clearStaticField(access, factAp, unchanged, propagateFact, propagateFactWithAccessorExclude)
        }

        val value = assignFrom?.takeUnless { it is AccessPathBase.Constant } ?: return
        val readValue = { fact: FinalFactAp, exclude: (FinalFactAp, Accessor) -> Unit ->
            super.fieldRead(value, access, fact, {}, { if (it.base == value) propagateFact(it) }, exclude)
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
        super.fieldWrite(classAccess, null, factAp, unchanged, propagateFact, propagateFactWithAccessorExclude)

        val classFields = AccessPathBase.LocalVar.create(-1)
        val restore = { fields: FinalFactAp ->
            val restored = fields.writeToAccessor(access.base, access.classStaticAccessor)
            if (restored == factAp) unchanged(restored) else propagateFact(restored)
        }

        super.fieldRead(classFields, classAccess, factAp, {}, { fields ->
            if (fields.base == classFields) {
                super.fieldWrite(RefAccess(classFields, access.accessor), null, fields, restore, restore) { _, accessor ->
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

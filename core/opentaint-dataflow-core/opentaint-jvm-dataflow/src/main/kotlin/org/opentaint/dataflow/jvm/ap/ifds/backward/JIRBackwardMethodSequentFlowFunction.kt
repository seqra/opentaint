package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.MemoryAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.RefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.StaticRefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.writeToAccessor
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRMethodSequentFlowFunction
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.jvm.graph.JMethodEnterInst

class JIRBackwardMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val currentInst: JIRInst,
) : JIRMethodSequentFlowFunction(apManager, analysisContext, currentInst, generateTrace = false) {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        val demands = when (currentInst) {
            is JIRReturnInst -> rules.methodExitSinkDemands(currentInst)
            is JMethodEnterInst -> rules.methodEntrySinkDemands(currentInst)
            else -> emptyList()
        }

        rules.recordSinkDemands(currentInst, demands).mapTo(this) { Sequent.ZeroToFact(it, TraceInfo.Flow) }
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
                val sources = rules.matchStaticFieldSources(currentInst, factAp)
                val reader = sources.reader ?: return super.propagate(
                    initialFacts, factAp, unchanged, propagateFact,
                    propagateFactWithRefinement, propagateFactWithAccessorExclude, sideEffect
                )

                rules.recordSourceMatches(sources)
                refiner.add(reader)
                super.propagate(
                    initialFacts, factAp, { demands += factAp }, { fact, _ -> demands += fact },
                    propagateFactWithRefinement, propagateFactWithAccessorExclude, sideEffect
                )
                demands += sources.conditionDemands
            }

            is JIRReturnInst -> {
                rules.matchEndRequirement(currentInst, factAp)?.let(refiner::add)
                val sources = rules.matchMethodExitSources(currentInst, factAp)
                rules.recordSourceMatches(sources)
                sources.reader?.let(refiner::add)

                val returnValue = currentInst.returnValue?.let { accessPathBase(it) }
                simpleAssign(AccessPathBase.Return, returnValue, factAp, demands::add, demands::add)
                demands += sources.conditionDemands
            }

            is JIRThrowInst -> {
                val throwable = accessPathBase(currentInst.throwable)
                simpleAssign(AccessPathBase.Exception, throwable, factAp, demands::add, demands::add)
            }

            is JMethodEnterInst -> {
                rules.matchEndRequirement(currentInst, factAp)?.let(refiner::add)
                val sources = rules.matchMethodEntrySources(currentInst, factAp)
                rules.recordMethodEntrySourceMatches(currentInst, sources, initialFacts.orEmpty())
                sources.reader?.let(refiner::add)

                if (!initialFacts.isNullOrEmpty() || rules.keepsZeroEdgeDemandsAtMethodEnter(currentInst)) {
                    demands += factAp
                    demands += sources.conditionDemands
                }
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

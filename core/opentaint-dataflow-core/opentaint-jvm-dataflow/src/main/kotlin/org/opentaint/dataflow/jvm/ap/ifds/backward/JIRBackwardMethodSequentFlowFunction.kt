package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.Sequent
import org.opentaint.dataflow.ap.ifds.analysis.MethodSequentFlowFunction.TraceInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.excludeField
import org.opentaint.dataflow.jvm.ap.ifds.analysis.apAccessor
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.ir.api.jvm.cfg.JIRValue
import org.opentaint.jvm.graph.JMethodEnterInst

class JIRBackwardMethodSequentFlowFunction(
    private val apManager: ApManager,
    private val analysisContext: JIRBackwardMethodAnalysisContext,
    private val currentInst: JIRInst,
) : MethodSequentFlowFunction {
    private val rules by lazy { JIRBackwardTaintRules(apManager, analysisContext) }
    private val factTypeChecker get() = analysisContext.factTypeChecker

    override fun propagateZeroToZero(): Set<Sequent> = buildSet {
        add(Sequent.ZeroToZero)

        val demands = when (currentInst) {
            is JIRReturnInst -> rules.methodExitSinkDemands(currentInst)
            is JMethodEnterInst -> rules.methodEntrySinkDemands(currentInst)
            else -> emptyList()
        }

        rules.recordSinkDemands(currentInst, demands).forEach { seed ->
            add(Sequent.ZeroToFact(seed, TraceInfo.Flow))
        }
    }

    override fun propagateZeroToFact(currentFactAp: FinalFactAp): Set<Sequent> = buildSet {
        propagate(
            DemandOutput(
                current = currentFactAp,
                unchanged = { add(Sequent.Unchanged) },
                propagateFact = { fact -> add(Sequent.ZeroToFact(fact, TraceInfo.Flow)) },
                propagateFactWithRefinement = { reader, fact ->
                    check(!reader.hasRefinement) {
                        "Zero to Fact edge can't be refined: $currentFactAp"
                    }
                    add(Sequent.ZeroToFact(fact, TraceInfo.Flow))
                },
                propagateFactWithAccessorExclude = { _, _ ->
                    error("Zero to Fact edge can't be refined: $currentFactAp")
                },
            )
        )
    }

    override fun propagateFactToFact(initialFactAp: InitialFactAp, currentFactAp: FinalFactAp): Set<Sequent> =
        buildSet {
            propagate(
                DemandOutput(
                    current = currentFactAp,
                    unchanged = { add(Sequent.Unchanged) },
                    propagateFact = { fact -> add(Sequent.FactToFact(initialFactAp, fact, TraceInfo.Flow)) },
                    propagateFactWithRefinement = { reader, fact ->
                        val refinedInitial = reader.refineFact(initialFactAp)
                        val refinedFact = reader.refineFact(fact)
                        add(Sequent.FactToFact(refinedInitial, refinedFact, TraceInfo.Flow))
                    },
                    propagateFactWithAccessorExclude = { fact, accessor ->
                        val refinedInitial = initialFactAp.excludeField(accessor)
                        val refinedFact = fact.excludeField(accessor)
                        add(Sequent.FactToFact(refinedInitial, refinedFact, TraceInfo.Flow))
                    },
                )
            )
        }

    override fun propagateNDFactToFact(initialFacts: Set<InitialFactAp>, currentFactAp: FinalFactAp): Set<Sequent> =
        buildSet {
            propagate(
                DemandOutput(
                    current = currentFactAp,
                    unchanged = { add(Sequent.Unchanged) },
                    propagateFact = { fact -> add(Sequent.NDFactToFact(initialFacts, fact, TraceInfo.Flow)) },
                    propagateFactWithRefinement = { reader, fact ->
                        check(!reader.hasRefinement) {
                            "NDF2F edge can't be refined: $currentFactAp"
                        }
                        add(Sequent.NDFactToFact(initialFacts, fact, TraceInfo.Flow))
                    },
                    propagateFactWithAccessorExclude = { _, _ ->
                        error("NDF2F edge can't be refined: $currentFactAp")
                    },
                )
            )
        }

    private class DemandOutput(
        val current: FinalFactAp,
        val unchanged: () -> Unit,
        val propagateFact: (FinalFactAp) -> Unit,
        val propagateFactWithRefinement: (FinalFactReader, FinalFactAp) -> Unit,
        val propagateFactWithAccessorExclude: (FinalFactAp, Accessor) -> Unit,
    ) {
        fun keep(fact: FinalFactAp) {
            if (fact == current) unchanged() else propagateFact(fact)
        }

        fun keepAll(reader: FinalFactReader?, facts: List<FinalFactAp>) {
            if (reader != null && reader.hasRefinement) {
                facts.forEach { propagateFactWithRefinement(reader, it) }
            } else {
                facts.forEach { keep(it) }
            }
        }
    }

    private fun propagate(out: DemandOutput) {
        val fact = out.current
        when (currentInst) {
            is JIRAssignInst -> assign(currentInst, fact, out)
            is JIRReturnInst -> methodExit(currentInst, fact, out)
            is JIRThrowInst -> {
                val demand = exitValueDemand(AccessPathBase.Exception, accessPathBase(currentInst.throwable), fact)
                demand?.let { out.keep(it) }
            }

            is JMethodEnterInst -> methodEnter(fact, out)
            else -> out.unchanged()
        }
    }

    private fun methodExit(inst: JIRReturnInst, fact: FinalFactAp, out: DemandOutput) {
        val sources = rules.matchMethodExitSources(inst, fact)
        rules.recordSourceMatches(inst, sources)

        val demands = mutableListOf<FinalFactAp>()
        val returnBase = inst.returnValue?.let { accessPathBase(it) }
        exitValueDemand(AccessPathBase.Return, returnBase, fact)?.let { demands += it }
        demands += sources.conditionDemands

        out.keepAll(sources.reader, demands)
    }

    private fun exitValueDemand(exitBase: AccessPathBase, valueBase: AccessPathBase?, fact: FinalFactAp): FinalFactAp? {
        if (fact.base != exitBase) return fact
        val base = valueBase?.takeUnless { it is AccessPathBase.Constant } ?: return null
        return fact.rebase(base)
    }

    private fun methodEnter(fact: FinalFactAp, out: DemandOutput) {
        val sources = rules.matchMethodEntrySources(currentInst, fact)
        rules.recordSourceMatches(currentInst, sources)
        out.keepAll(sources.reader, listOf(fact) + sources.conditionDemands)
    }

    private fun assign(inst: JIRAssignInst, currentFact: FinalFactAp, out: DemandOutput) {
        val fact = filterAssignFact(inst.lhv, inst.rhv, currentFact) ?: return
        val assignTo = MethodFlowFunctionUtils.mkAccess(inst.lhv)
        if (assignTo == null) {
            out.keep(fact)
            return
        }

        when (assignTo) {
            is MethodFlowFunctionUtils.Simple -> assignToLocal(inst, assignTo.base, fact, out)

            is MethodFlowFunctionUtils.RefAccess -> {
                val assignFrom = valueBase(inst.rhv)
                if (assignTo.accessor is ElementAccessor) {
                    arrayWrite(assignTo.base, assignFrom, fact, out)
                } else {
                    fieldWrite(assignTo.base, assignTo.accessor, assignFrom, fact, out)
                }
            }

            is MethodFlowFunctionUtils.StaticRefAccess -> {
                if (fact.base != AccessPathBase.ClassStatic) {
                    out.keep(fact)
                    return
                }

                val accessors = listOf(assignTo.classStaticAccessor, assignTo.accessor)
                strongWrite(fact, accessors, idx = 0, wrap = { it }, valueBase(inst.rhv), out)
            }
        }
    }

    private fun assignToLocal(inst: JIRAssignInst, assignTo: AccessPathBase, fact: FinalFactAp, out: DemandOutput) {
        if (fact.base != assignTo) {
            out.keep(fact)
            return
        }

        val rhv = inst.rhv
        val assignFrom = when (rhv) {
            is JIRCastExpr -> listOfNotNull(MethodFlowFunctionUtils.mkAccess(rhv.operand))
            is JIRImmediate -> listOfNotNull(MethodFlowFunctionUtils.mkAccess(rhv))
            is JIRFieldRef -> listOfNotNull(MethodFlowFunctionUtils.mkAccess(rhv))
            is JIRArrayAccess -> listOfNotNull(MethodFlowFunctionUtils.mkAccess(rhv))
            is JIRBinaryExpr -> listOfNotNull(
                MethodFlowFunctionUtils.mkAccess(rhv.lhv),
                MethodFlowFunctionUtils.mkAccess(rhv.rhv),
            )

            else -> emptyList()
        }

        for (access in assignFrom) {
            when (access) {
                is MethodFlowFunctionUtils.Simple -> {
                    if (access.base is AccessPathBase.Constant) continue
                    out.keep(fact.rebase(access.base))
                }

                is MethodFlowFunctionUtils.RefAccess -> {
                    out.propagateFact(fact.prependAccessor(access.accessor).rebase(access.base))
                }

                is MethodFlowFunctionUtils.StaticRefAccess -> {
                    val sources = rules.matchStaticFieldSources(inst, fact)
                    rules.recordSourceMatches(inst, sources)

                    val staticFact = fact
                        .prependAccessor(access.accessor)
                        .prependAccessor(access.classStaticAccessor)
                        .rebase(AccessPathBase.ClassStatic)

                    out.keepAll(sources.reader, listOf(staticFact) + sources.conditionDemands)
                }
            }
        }
    }

    private fun fieldWrite(
        instance: AccessPathBase,
        accessor: Accessor,
        assignFrom: AccessPathBase?,
        fact: FinalFactAp,
        out: DemandOutput,
    ) {
        if (fact.base == instance) {
            strongWrite(fact, listOf(accessor), idx = 0, wrap = { it }, assignFrom, out)
            return
        }

        out.keep(fact)

        forEachWriteAlias(instance, fact, out) { aliased ->
            moveWrittenValue(aliased, accessor, assignFrom, fact, out)
        }
    }

    private fun arrayWrite(
        instance: AccessPathBase,
        assignFrom: AccessPathBase?,
        fact: FinalFactAp,
        out: DemandOutput,
    ) {
        out.keep(fact)

        if (fact.base == instance) {
            moveWrittenValue(fact, ElementAccessor, assignFrom, fact.abstractOnlyIfAbstract(), out)
            return
        }

        forEachWriteAlias(instance, fact, out) { aliased ->
            moveWrittenValue(aliased, ElementAccessor, assignFrom, fact, out)
        }
    }

    private fun FinalFactAp.abstractOnlyIfAbstract(): FinalFactAp =
        if (isAbstract()) abstractOnly() else this

    private fun strongWrite(
        fact: FinalFactAp,
        accessors: List<Accessor>,
        idx: Int,
        wrap: (FinalFactAp) -> FinalFactAp,
        assignFrom: AccessPathBase?,
        out: DemandOutput,
    ) {
        val accessor = accessors[idx]

        if (fact.isAbstract() && accessor !in fact.exclusions) {
            fact.removeAbstraction()?.let { nonAbstract ->
                strongWrite(nonAbstract, accessors, idx, wrap, assignFrom, out)
            }

            out.propagateFactWithAccessorExclude(wrap(fact.abstractOnly()), accessor)
            return
        }

        if (!fact.startsWithAccessor(accessor)) {
            out.keep(wrap(fact))
            return
        }

        fact.clearAccessor(accessor)?.let { out.keep(wrap(it)) }

        val written = fact.readAccessor(accessor) ?: return
        if (idx == accessors.lastIndex) {
            assignFrom?.let { out.propagateFact(written.rebase(it)) }
            return
        }

        strongWrite(written, accessors, idx + 1, { wrap(it.prependAccessor(accessor)) }, assignFrom, out)
    }

    private fun moveWrittenValue(
        fact: FinalFactAp,
        accessor: Accessor,
        assignFrom: AccessPathBase?,
        refinementTarget: FinalFactAp,
        out: DemandOutput,
    ) {
        if (fact.isAbstract() && accessor !in fact.exclusions) {
            fact.removeAbstraction()?.let { nonAbstract ->
                moveWrittenValue(nonAbstract, accessor, assignFrom, refinementTarget, out)
            }

            out.propagateFactWithAccessorExclude(refinementTarget, accessor)
            return
        }

        if (!fact.startsWithAccessor(accessor)) return

        val written = fact.readAccessor(accessor) ?: return
        assignFrom?.let { out.propagateFact(written.rebase(it)) }
    }

    private inline fun forEachWriteAlias(
        instance: AccessPathBase,
        fact: FinalFactAp,
        out: DemandOutput,
        body: (FinalFactAp) -> Unit,
    ) {
        val aliasAnalysis = analysisContext.aliasAnalysis ?: return
        val instanceLocal = instance as? AccessPathBase.LocalVar ?: return

        val aliases = aliasAnalysis.findAlias(instanceLocal, currentInst) ?: return
        for (alias in aliases) {
            if (alias !is AliasApInfo || alias.base != fact.base) continue

            var aliased: FinalFactAp? = fact
            for (aliasAccessor in alias.accessors) {
                val current = aliased ?: break
                val accessor = aliasAccessor.apAccessor()
                if (current.isAbstract() && accessor !in current.exclusions) {
                    out.propagateFactWithAccessorExclude(fact, accessor)
                }
                aliased = current.readAccessor(accessor)
            }

            aliased?.let { body(it.rebase(instance)) }
        }
    }

    private fun valueBase(value: JIRExpr): AccessPathBase? {
        val access = (value as? JIRValue)?.let { MethodFlowFunctionUtils.mkAccess(it) }
        val simple = access as? MethodFlowFunctionUtils.Simple ?: return null
        return simple.base.takeUnless { it is AccessPathBase.Constant }
    }

    private fun filterAssignFact(assignTo: JIRValue, assignFrom: JIRExpr, fact: FinalFactAp): FinalFactAp? {
        val filtered = filterAssignFromFact(assignFrom, fact) ?: return null
        return filterValueFact(assignTo, filtered)
    }

    private fun filterAssignFromFact(assignFrom: JIRExpr, fact: FinalFactAp): FinalFactAp? = when (assignFrom) {
        is JIRCastExpr -> filterBaseType(assignFrom.operand, assignFrom.type, fact)
        is JIRBinaryExpr -> filterValueFact(assignFrom.lhv, fact)?.let { filterValueFact(assignFrom.rhv, it) }
        is JIRValue -> filterValueFact(assignFrom, fact)
        else -> fact
    }

    private fun filterValueFact(value: JIRValue, fact: FinalFactAp): FinalFactAp? = when (value) {
        is JIRImmediate -> filterBaseType(value, value.type, fact)
        is JIRArrayAccess -> filterBaseType(value, value.array.type, fact)
        is JIRFieldRef -> filterBaseType(value, value.instance?.type, fact)
            ?.let { filterBaseType(value, value.field.enclosingType, it) }

        else -> fact
    }

    private fun filterBaseType(value: JIRValue, expectedType: JIRType?, fact: FinalFactAp): FinalFactAp? {
        val access = MethodFlowFunctionUtils.mkAccess(value) ?: return fact
        if (fact.base != access.base || expectedType == null) return fact
        return factTypeChecker.filterFactByLocalType(expectedType, fact)
    }
}

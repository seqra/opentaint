package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.TaintRulePrecondition
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.dataflow.go.analysis.GoMethodAnalysisContext
import org.opentaint.dataflow.go.analysis.applyGlobalOrFieldReadSourceRules
import org.opentaint.dataflow.go.analysis.forEachPossibleAliasAtStatement
import org.opentaint.dataflow.taint.InitialFactReader
import org.opentaint.dataflow.taint.TaintSourceActionPreconditionEvaluator
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.expr.GoIRExpr
import org.opentaint.ir.go.expr.GoIRLookupExpr
import org.opentaint.ir.go.expr.GoIRMakeClosureExpr
import org.opentaint.ir.go.expr.GoIRNextExpr
import org.opentaint.ir.go.expr.GoIRTypeAssertExpr
import org.opentaint.ir.go.expr.GoIRUnOpExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRFieldStore
import org.opentaint.ir.go.inst.GoIRGlobalStore
import org.opentaint.ir.go.inst.GoIRIndexStore
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.type.GoIRBinaryOp

class GoMethodSequentPrecondition(
    private val apManager: ApManager,
    private val currentInst: GoIRInst,
    private val analysisContext: GoMethodAnalysisContext,
) : MethodSequentPrecondition {

    private val method: GoIRFunction get() = analysisContext.method

    override fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition> {
        val result = hashSetOf<SequentPrecondition>()
        result.computeFactPrecondition(fact)
        return result
    }

    private fun MutableSet<SequentPrecondition>.computeFactPrecondition(fact: InitialFactAp) {
        this += computePrecondition(fact).ifEmpty { setOf(SequentPrecondition.Unchanged) }

        analysisContext.aliasAnalysis.forEachPossibleAliasAtStatement(currentInst, fact) { aliasedFact ->
            this += computePrecondition(aliasedFact)
        }
    }

    private fun computePrecondition(fact: InitialFactAp): Set<SequentPrecondition> {
        val result = hashSetOf<SequentPrecondition>()
        preconditionForFact(fact)?.let {
            result += PreconditionFactsForInitialFact(fact, it)
        }
        result.unconditionalGlobalOrFieldReadSourceRulePrecondition(fact)
        return result
    }

    private fun preconditionForFact(fact: InitialFactAp): List<InitialFactAp>? =
        when (val inst = currentInst) {
            is GoIRAssignInst -> assignPrecondition(inst, fact)
            is GoIRStore -> ptrStorePrecondition(inst, fact)
            is GoIRFieldStore -> fieldStorePrecondition(inst, fact)
            is GoIRIndexStore -> indexStorePrecondition(inst, fact)
            is GoIRGlobalStore -> globalStorePrecondition(inst, fact)
            is GoIRReturn -> returnPrecondition(inst, fact)
            is GoIRPhi -> phiPrecondition(inst, fact)
            is GoIRMapUpdate -> mapUpdatePrecondition(inst, fact)
            is GoIRSend -> sendPrecondition(inst, fact)
            else -> null
        }

    private fun assignPrecondition(inst: GoIRAssignInst, fact: InitialFactAp): List<InitialFactAp>? {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        val expr = inst.expr

        if (expr.isCommaOk()) {
            return commaOkPrecondition(expr, registerBase, fact)
        }

        if (expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD && GoFlowFunctionUtils.isStringType(expr.type)) {
            return stringConcatPrecondition(fact, registerBase, expr)
        }

        if (expr is GoIRMakeClosureExpr) {
            return makeClosurePrecondition(fact, registerBase, expr)
        }

        if (expr is GoIRNextExpr) {
            return nextPrecondition(fact, registerBase, expr)
        }

        return assignedExprPrecondition(expr, registerBase, fact)
    }

    private fun GoIRExpr.isCommaOk(): Boolean = when (this) {
        is GoIRLookupExpr -> commaOk
        is GoIRTypeAssertExpr -> commaOk
        is GoIRUnOpExpr -> commaOk
        else -> false
    }

    private fun assignedExprPrecondition(
        expr: GoIRExpr,
        registerBase: AccessPathBase,
        fact: InitialFactAp,
    ): List<InitialFactAp>? {
        val rhsAccess = GoFlowFunctionUtils.exprToAccess(expr, method)
            ?: return if (fact.base == registerBase) emptyList() else null

        return when (rhsAccess) {
            is Access.Simple -> simpleAssignPrecondition(registerBase, rhsAccess.base, fact)
            is Access.RefAccess -> refReadPrecondition(registerBase, rhsAccess, fact)
        }
    }

    private fun simpleAssignPrecondition(
        toBase: AccessPathBase,
        fromBase: AccessPathBase,
        fact: InitialFactAp,
    ): List<InitialFactAp>? {
        if (fact.base != toBase) return null
        if (fromBase == toBase) return null
        return listOf(fact.rebase(fromBase))
    }

    private fun refReadPrecondition(
        toBase: AccessPathBase,
        rhsAccess: Access.RefAccess,
        fact: InitialFactAp,
    ): List<InitialFactAp>? {
        if (fact.base != toBase) return null
        return listOf(fact.prependAccessor(rhsAccess.accessor).rebase(rhsAccess.base))
    }

    private fun commaOkPrecondition(
        expr: GoIRExpr,
        registerBase: AccessPathBase,
        fact: InitialFactAp,
    ): List<InitialFactAp>? {
        if (fact.base != registerBase) {
            return assignedExprPrecondition(expr, registerBase, fact)
        }

        val valueSlot = GoFlowFunctionUtils.tupleFieldAccessor(0)
        if (!fact.startsWithAccessor(valueSlot)) {
            return emptyList()
        }

        val stripped = fact.readAccessor(valueSlot) ?: return emptyList()
        return assignedExprPrecondition(expr, registerBase, stripped)
    }

    private fun stringConcatPrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
        expr: GoIRBinOpExpr,
    ): List<InitialFactAp>? {
        if (fact.base != registerBase) return null

        val leftBase = GoFlowFunctionUtils.accessPathBase(expr.x, method)
        val rightBase = GoFlowFunctionUtils.accessPathBase(expr.y, method)
        return listOf(fact.rebase(leftBase), fact.rebase(rightBase))
    }

    private fun makeClosurePrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
        expr: GoIRMakeClosureExpr,
    ): List<InitialFactAp>? {
        if (fact.base != registerBase) return null

        val pres = mutableListOf<InitialFactAp>()
        for ((i, binding) in expr.bindings.withIndex()) {
            val accessor = GoFlowFunctionUtils.freeVarAccessor(expr.fn, i)
            if (!fact.startsWithAccessor(accessor)) continue
            val stripped = fact.readAccessor(accessor) ?: continue
            val bindingBase = GoFlowFunctionUtils.accessPathBase(binding, method)
            pres += stripped.rebase(bindingBase)
        }
        return pres
    }

    private fun nextPrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
        expr: GoIRNextExpr,
    ): List<InitialFactAp>? {
        if (fact.base != registerBase) return null

        val iterBase = GoFlowFunctionUtils.accessPathBase(expr.iter, method)
        val pres = mutableListOf<InitialFactAp>()
        for (slot in GoFlowFunctionUtils.rangeElementTupleSlots(expr, method)) {
            if (!fact.startsWithAccessor(slot)) continue
            val stripped = fact.readAccessor(slot) ?: continue
            pres += stripped.prependAccessor(ElementAccessor).rebase(iterBase)
        }
        return pres
    }

    private fun ptrStorePrecondition(inst: GoIRStore, fact: InitialFactAp): List<InitialFactAp>? {
        val dstBase = GoFlowFunctionUtils.accessPathBase(inst.addr, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        return simpleAssignPrecondition(dstBase, valueBase, fact)
    }

    private fun fieldStorePrecondition(inst: GoIRFieldStore, fact: InitialFactAp): List<InitialFactAp>? {
        val instance = GoFlowFunctionUtils.accessPathBase(inst.base, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val accessor = GoFlowFunctionUtils.fieldAccessorFromStore(inst)
        return accessorWritePrecondition(instance, accessor, listOf(valueBase), fact)
    }

    private fun indexStorePrecondition(inst: GoIRIndexStore, fact: InitialFactAp): List<InitialFactAp>? {
        val instance = GoFlowFunctionUtils.accessPathBase(inst.base, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        return accessorWritePrecondition(instance, ElementAccessor, listOf(valueBase), fact)
    }

    private fun globalStorePrecondition(inst: GoIRGlobalStore, fact: InitialFactAp): List<InitialFactAp>? {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val globalAccess = GoFlowFunctionUtils.accessForGlobal(inst.global)
        return accessorWritePrecondition(globalAccess.base, globalAccess.accessor, listOf(valueBase), fact)
    }

    private fun mapUpdatePrecondition(inst: GoIRMapUpdate, fact: InitialFactAp): List<InitialFactAp>? {
        val mapBase = GoFlowFunctionUtils.accessPathBase(inst.map, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method)
        val keyBase = GoFlowFunctionUtils.accessPathBase(inst.key, method)
        val sources = if (keyBase == valueBase) listOf(valueBase) else listOf(valueBase, keyBase)
        return accessorWritePrecondition(mapBase, ElementAccessor, sources, fact)
    }

    private fun sendPrecondition(inst: GoIRSend, fact: InitialFactAp): List<InitialFactAp>? {
        val chanBase = GoFlowFunctionUtils.accessPathBase(inst.chan, method)
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.x, method)
        return accessorWritePrecondition(chanBase, ElementAccessor, listOf(valueBase), fact)
    }

    private fun accessorWritePrecondition(
        destBase: AccessPathBase,
        accessor: Accessor,
        valueBases: List<AccessPathBase>,
        fact: InitialFactAp,
    ): List<InitialFactAp>? {
        if (fact.base != destBase) return null
        if (!fact.startsWithAccessor(accessor)) return null

        val factAtAccessor = fact.readAccessor(accessor) ?: return null

        val pres = mutableListOf<InitialFactAp>()
        valueBases.mapTo(pres) { factAtAccessor.rebase(it) }

        fact.clearAccessor(accessor)?.let { pres += it }

        if (accessor is ElementAccessor) {
            pres += factAtAccessor.prependAccessor(ElementAccessor)
        }

        return pres
    }

    private fun returnPrecondition(inst: GoIRReturn, fact: InitialFactAp): List<InitialFactAp>? {
        if (fact.base !is AccessPathBase.Return) return null

        if (inst.results.size == 1) {
            val retBase = GoFlowFunctionUtils.accessPathBase(inst.results[0], method)
            return listOf(fact.rebase(retBase))
        }

        val pres = mutableListOf<InitialFactAp>()
        for ((i, retVal) in inst.results.withIndex()) {
            val tupleAccessor = GoFlowFunctionUtils.tupleFieldAccessor(i)
            if (!fact.startsWithAccessor(tupleAccessor)) continue
            val stripped = fact.readAccessor(tupleAccessor) ?: continue
            pres += stripped.rebase(GoFlowFunctionUtils.accessPathBase(retVal, method))
        }
        return pres
    }

    private fun phiPrecondition(inst: GoIRPhi, fact: InitialFactAp): List<InitialFactAp>? {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        if (fact.base != registerBase) return null

        return inst.edges.values.map { edge ->
            fact.rebase(GoFlowFunctionUtils.accessPathBase(edge, method))
        }
    }

    private fun MutableSet<SequentPrecondition>.unconditionalGlobalOrFieldReadSourceRulePrecondition(
        fact: InitialFactAp,
    ) {
        val inst = currentInst as? GoIRAssignInst ?: return
        val lhv = AccessPathBase.LocalVar(inst.register.index)
        if (fact.base != lhv) return

        applyGlobalOrFieldReadSourceRules(
            currentInst, analysisContext,
            mkSourceEvaluator = {
                val entryFactReader = InitialFactReader(fact.rebase(AccessPathBase.Return), apManager)
                TaintSourceActionPreconditionEvaluator(entryFactReader)
            }
        ) { rule, action, _, _ ->
            this += MethodSequentPrecondition.SequentSource(
                fact, TaintRulePrecondition.Source(rule, setOf(action)),
            )
        }
    }
}

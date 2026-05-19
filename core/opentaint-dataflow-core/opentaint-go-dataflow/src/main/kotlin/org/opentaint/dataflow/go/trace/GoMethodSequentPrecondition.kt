package org.opentaint.dataflow.go.trace

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.PreconditionFactsForInitialFact
import org.opentaint.dataflow.ap.ifds.trace.MethodSequentPrecondition.SequentPrecondition
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.go.GoFlowFunctionUtils.Access
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.expr.GoIRBinOpExpr
import org.opentaint.ir.go.inst.GoIRAssignInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.inst.GoIRMapUpdate
import org.opentaint.ir.go.inst.GoIRPhi
import org.opentaint.ir.go.inst.GoIRReturn
import org.opentaint.ir.go.inst.GoIRSend
import org.opentaint.ir.go.inst.GoIRStore
import org.opentaint.ir.go.type.GoIRBinaryOp

/**
 * Sequent (intra-procedural) precondition for Go statements. For an out-fact computed
 * after [currentInst], returns the set of in-facts that could have produced it via the
 * corresponding flow function ([org.opentaint.dataflow.go.analysis.GoMethodSequentFlowFunction]).
 */
class GoMethodSequentPrecondition(
    private val currentInst: GoIRInst,
    private val method: GoIRFunction,
) : MethodSequentPrecondition {

    override fun factPrecondition(fact: InitialFactAp): Set<SequentPrecondition> {
        val preconditionFacts = preconditionForFact(fact)
            ?: return setOf(SequentPrecondition.Unchanged)

        val result = hashSetOf<SequentPrecondition>()
        result += PreconditionFactsForInitialFact(fact, preconditionFacts)
        return result
    }

    private fun preconditionForFact(fact: InitialFactAp): List<InitialFactAp>? {
        return when (val inst = currentInst) {
            is GoIRAssignInst -> handleAssign(inst, fact)
            is GoIRStore -> handleStore(inst, fact)
            is GoIRReturn -> handleReturn(inst, fact)
            is GoIRPhi -> handlePhi(inst, fact)
            is GoIRMapUpdate -> handleMapUpdate(inst, fact)
            is GoIRSend -> handleSend(inst, fact)
            else -> null
        }
    }

    private fun handleAssign(inst: GoIRAssignInst, fact: InitialFactAp): List<InitialFactAp>? {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        val expr = inst.expr

        if (expr is GoIRBinOpExpr && expr.op == GoIRBinaryOp.ADD
            && GoFlowFunctionUtils.isStringType(expr.type)
        ) {
            return handleStringConcatPrecondition(fact, registerBase, expr)
        }

        val rhsAccess = GoFlowFunctionUtils.exprToAccess(expr, method)
            ?: return handleNonPropagatingPrecondition(fact, registerBase)

        return when (rhsAccess) {
            is Access.Simple -> handleSimpleAssignPrecondition(fact, registerBase, rhsAccess.base)
            is Access.RefAccess -> handleRefAssignPrecondition(fact, registerBase, rhsAccess)
        }
    }

    private fun handleSimpleAssignPrecondition(
        fact: InitialFactAp,
        toBase: AccessPathBase,
        fromBase: AccessPathBase,
    ): List<InitialFactAp>? {
        if (fact.base == toBase) {
            // Fact lives on the destination after assignment: must have been on source before.
            if (fromBase == toBase) return null // unchanged
            return listOf(fact.rebase(fromBase))
        }
        // Fact is unrelated to the destination — unchanged.
        return null
    }

    private fun handleRefAssignPrecondition(
        fact: InitialFactAp,
        toBase: AccessPathBase,
        rhsAccess: Access.RefAccess,
    ): List<InitialFactAp>? {
        if (fact.base != toBase) {
            // unchanged
            return null
        }

        // Fact is on the destination register after `toBase = rhsAccess.base.accessor`.
        // Precondition: fact had been at `rhsAccess.base` with `accessor` prepended.
        val newFact = fact.prependAccessor(rhsAccess.accessor).rebase(rhsAccess.base)
        return listOf(newFact)
    }

    private fun handleStore(inst: GoIRStore, fact: InitialFactAp): List<InitialFactAp>? {
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method) ?: return null
        val addrAccess = GoFlowFunctionUtils.accessForAddr(inst.addr, method) ?: return null

        when (addrAccess) {
            is Access.RefAccess -> {
                val destBase = addrAccess.base
                val accessor = addrAccess.accessor

                if (fact.base != destBase) return null // unchanged

                // Strong update on FieldAccessor: the stored value replaces what was at `accessor`.
                // Weak update on ElementAccessor: prior `accessor` content is preserved.
                if (!fact.startsWithAccessor(accessor)) return null

                val stripped = fact.readAccessor(accessor) ?: return null
                val result = mutableListOf<InitialFactAp>()
                // The fact under `accessor` could have come from the stored `value`.
                result += stripped.rebase(valueBase)
                if (accessor is ElementAccessor) {
                    // Weak update: the same accessor structure may have existed before, too.
                    result += fact
                }
                return result
            }

            is Access.Simple -> {
                val destBase = addrAccess.base
                if (fact.base != destBase) return null // unchanged
                return listOf(fact.rebase(valueBase))
            }
        }
    }

    private fun handleReturn(inst: GoIRReturn, fact: InitialFactAp): List<InitialFactAp>? {
        if (fact.base !is AccessPathBase.Return) return null

        if (inst.results.size == 1) {
            val retBase = GoFlowFunctionUtils.accessPathBase(inst.results[0], method) ?: return null
            return listOf(fact.rebase(retBase))
        }

        val result = mutableListOf<InitialFactAp>()
        for ((i, retVal) in inst.results.withIndex()) {
            val retBase = GoFlowFunctionUtils.accessPathBase(retVal, method) ?: continue
            val tupleAccessor: Accessor = GoFlowFunctionUtils.tupleFieldAccessor(i, retVal.type)
            if (!fact.startsWithAccessor(tupleAccessor)) continue
            val stripped = fact.readAccessor(tupleAccessor) ?: continue
            result += stripped.rebase(retBase)
        }
        if (result.isEmpty()) return null
        return result
    }

    private fun handlePhi(inst: GoIRPhi, fact: InitialFactAp): List<InitialFactAp>? {
        val registerBase = AccessPathBase.LocalVar(inst.register.index)
        if (fact.base != registerBase) return null

        val result = mutableListOf<InitialFactAp>()
        for (edge in inst.edges.values) {
            val edgeBase = GoFlowFunctionUtils.accessPathBase(edge, method) ?: continue
            result += fact.rebase(edgeBase)
        }
        if (result.isEmpty()) return null
        return result
    }

    private fun handleMapUpdate(inst: GoIRMapUpdate, fact: InitialFactAp): List<InitialFactAp>? {
        val mapBase = GoFlowFunctionUtils.accessPathBase(inst.map, method) ?: return null
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.value, method) ?: return null

        if (fact.base != mapBase) return null
        if (!fact.startsWithAccessor(ElementAccessor)) return null

        val stripped = fact.readAccessor(ElementAccessor) ?: return null
        // Weak update: keep original fact plus the value-derived precondition.
        return listOf(stripped.rebase(valueBase), fact)
    }

    private fun handleSend(inst: GoIRSend, fact: InitialFactAp): List<InitialFactAp>? {
        val chanBase = GoFlowFunctionUtils.accessPathBase(inst.chan, method) ?: return null
        val valueBase = GoFlowFunctionUtils.accessPathBase(inst.x, method) ?: return null

        if (fact.base != chanBase) return null
        if (!fact.startsWithAccessor(ElementAccessor)) return null

        val stripped = fact.readAccessor(ElementAccessor) ?: return null
        return listOf(stripped.rebase(valueBase), fact)
    }

    private fun handleStringConcatPrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
        expr: GoIRBinOpExpr,
    ): List<InitialFactAp>? {
        if (fact.base != registerBase) return null

        val result = mutableListOf<InitialFactAp>()
        GoFlowFunctionUtils.accessPathBase(expr.x, method)?.let { result += fact.rebase(it) }
        GoFlowFunctionUtils.accessPathBase(expr.y, method)?.let { result += fact.rebase(it) }
        if (result.isEmpty()) return null
        return result
    }

    private fun handleNonPropagatingPrecondition(
        fact: InitialFactAp,
        registerBase: AccessPathBase,
    ): List<InitialFactAp>? {
        if (fact.base == registerBase) {
            // Register overwritten with clean value — fact cannot have any precondition here.
            return emptyList()
        }
        return null
    }
}

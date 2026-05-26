package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.python.PIRFlowFunctionUtils.SELF_ACCESSOR
import org.opentaint.dataflow.python.adapter.PIRCallExprAdapter
import org.opentaint.dataflow.python.pIRDowncast
import org.opentaint.dataflow.python.util.PIRFlowFunctionUtils
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.python.*

/**
 * Maps facts between caller and callee frames at call boundaries.
 *
 * Offset-blind: the core mapping methods align `call.args[i]` with
 * callee `Argument(i)` positionally with no shift for `self`/`cls`.
 * All implicit-parameter offset arithmetic is encapsulated in
 * [offsetEnter] / [offsetExit], which are invoked only by
 * [PIRMethodCallResolver] and [PIRMethodCallSummaryHandler].
 */
object PIRMethodCallFactMapper : MethodCallFactMapper {

    private fun valueToBase(value: PIRValue): AccessPathBase? =
        PIRFlowFunctionUtils.accessPathBase(value)

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
    ): List<FinalFactAp> {
        val call = callStatement as PIRCall
        return when (val base = factAp.base) {
            is AccessPathBase.Argument -> {
                val argValue = call.args.getOrNull(base.idx)?.value ?: return emptyList()
                val callerBase = valueToBase(argValue) ?: return emptyList()
                listOf(factAp.rebase(callerBase))
            }
            is AccessPathBase.Return -> {
                val target = call.target ?: return emptyList()
                val targetBase = valueToBase(target) ?: return emptyList()
                listOf(factAp.rebase(targetBase))
            }
            is AccessPathBase.This -> {
                val callee = call.callee
                val calleeBase = valueToBase(callee) ?: return emptyList()
                listOf(factAp.rebase(calleeBase))
            }
            is AccessPathBase.LocalVar -> emptyList()  // Cannot escape
            is AccessPathBase.ClassStatic -> listOf(factAp)
            is AccessPathBase.Constant -> listOf(factAp)
            else -> emptyList()
        }
    }

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: InitialFactAp,
    ): List<InitialFactAp> {
        val call = callStatement as PIRCall
        return when (val base = factAp.base) {
            is AccessPathBase.Argument -> {
                val argValue = call.args.getOrNull(base.idx)?.value ?: return emptyList()
                val callerBase = valueToBase(argValue) ?: return emptyList()
                listOf(factAp.rebase(callerBase))
            }
            is AccessPathBase.Return -> {
                val target = call.target ?: return emptyList()
                val targetBase = valueToBase(target) ?: return emptyList()
                listOf(factAp.rebase(targetBase))
            }
            is AccessPathBase.LocalVar -> emptyList()
            is AccessPathBase.ClassStatic -> listOf(factAp)
            is AccessPathBase.Constant -> listOf(factAp)
            else -> emptyList()
        }
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
        onMappedFact: (FinalFactAp, AccessPathBase) -> Unit,
    ) {
        val call = (callExpr as PIRCallExprAdapter).pirCall
        val base = factAp.base

        for ((i, arg) in call.args.withIndex()) {
            val argBase = valueToBase(arg.value) ?: continue
            if (base == argBase) {
                val startBase = AccessPathBase.Argument(i)
                onMappedFact(factAp, startBase)
            }
        }

        if (valueToBase(call.callee) == base) {
            val selfFact = factAp.readAccessor(SELF_ACCESSOR)
            selfFact?.let { onMappedFact(it, AccessPathBase.This) }
        }

        if (base is AccessPathBase.ClassStatic) {
            onMappedFact(factAp, base)
        }
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        fact: InitialFactAp,
        onMappedFact: (InitialFactAp, AccessPathBase) -> Unit,
    ) {
        val call = (callExpr as PIRCallExprAdapter).pirCall
        val base = fact.base

        for ((i, arg) in call.args.withIndex()) {
            val argBase = valueToBase(arg.value) ?: continue
            if (base == argBase) {
                val startBase = AccessPathBase.Argument(i)
                onMappedFact(fact.rebase(startBase), startBase)
            }
        }

        if (base is AccessPathBase.ClassStatic) {
            onMappedFact(fact, base)
        }
    }

    override fun factIsRelevantToMethodCall(
        callStatement: CommonInst,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        factAp: FactAp,
    ): Boolean {
        pIRDowncast<PIRCall>(callStatement)
        pIRDowncast<PIRLocalVar?>(returnValue)
        pIRDowncast<PIRCallExprAdapter>(callExpr)

        return factIsRelevantToMethodCall(callStatement, returnValue, callExpr, factAp)
    }

    private fun factIsRelevantToMethodCall(
        callStatement: PIRCall,
        returnValue: PIRValue?,
        callExpr: PIRCallExprAdapter,
        factAp: FactAp,
    ): Boolean {
        val base = factAp.base
        if (base is AccessPathBase.ClassStatic || base is AccessPathBase.Constant) return true
        if (valueToBase(callStatement.callee) == base) return true

        for (arg in callStatement.args) {
            if (base == valueToBase(arg.value)) return true
        }

        if (returnValue != null) {
            if (base == valueToBase(returnValue)) return true
        }

        return false
    }

    override fun isValidMethodExitFact(factAp: FactAp): Boolean =
        factAp.base !is AccessPathBase.LocalVar

    /**
     * Translates a caller-frame [base] into the callee's frame when
     * entering [callee] at [callSite]. For implicit-parameter callees
     * (instance methods, classmethods), maps `Argument(i)` to
     * `Argument(i + offset)`. Other bases are returned unchanged.
     *
     * Returns null when the shifted Argument would exceed the callee's
     * formal parameter count (avoids AccessPathBaseStorage crashes on
     * extra positional args).
     *
     * Only invoked from [PIRMethodCallResolver].
     */
    fun offsetEnter(callSite: PIRCall, callee: PIRFunction, base: AccessPathBase): AccessPathBase? {
        if (base !is AccessPathBase.Argument) return base
        val offset = PIRFlowFunctionUtils.implicitParamOffset(callee)
        val newIdx = base.idx + offset
        if (newIdx >= callee.parameters.size) return null
        return AccessPathBase.Argument(newIdx)
    }

    /**
     * Inverse of [offsetEnter]: translates a callee-frame [base] back to
     * the caller's frame when returning from [callee] at [callSite]. Maps
     * `Argument(i)` to `Argument(i - offset)`. Returns null when the
     * shifted Argument would underflow (e.g. the implicit receiver slot,
     * which never escapes back to caller args).
     *
     * Only invoked from [PIRMethodCallSummaryHandler].
     */
    fun offsetExit(callSite: PIRCall, callee: PIRFunction, base: AccessPathBase): AccessPathBase? {
        if (base !is AccessPathBase.Argument) return base
        val offset = PIRFlowFunctionUtils.implicitParamOffset(callee)
        val newIdx = base.idx - offset
        if (newIdx < 0) return null
        return AccessPathBase.Argument(newIdx)
    }
}

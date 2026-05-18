package org.opentaint.dataflow.go

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.type.GoIRCallMode
import org.opentaint.ir.go.value.GoIRRegister
import org.opentaint.ir.go.value.GoIRValue

/**
 * Maps taint facts between caller and callee namespaces.
 * Singleton object analogous to JIRMethodCallFactMapper.
 */
object GoMethodCallFactMapper : MethodCallFactMapper {

    // ── Exit-to-Return (callee → caller) ─────────────────────────────

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
    ): List<FinalFactAp> {
        return mapMethodExitToReturnFlowFact(callStatement, factAp, FinalFactAp::rebase)
    }

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: InitialFactAp,
    ): List<InitialFactAp> {
        return mapMethodExitToReturnFlowFact(callStatement, factAp, InitialFactAp::rebase)
    }

    fun <F: FactAp> mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: F,
        rebase: F.(AccessPathBase) -> F
    ): List<F> {
        val goInst = callStatement as GoIRInst
        val callInfo = GoFlowFunctionUtils.extractCallInfo(goInst) ?: return emptyList()
        val method = goInst.location.functionBody.function
        val isInvoke = callInfo.receiver != null
        val argOffset = if (isInvoke) 1 else 0

        return when (factAp.base) {
            is AccessPathBase.Return -> {
                val resultRegister = GoFlowFunctionUtils.extractResultRegister(goInst)
                    ?: return emptyList()
                listOf(factAp.rebase(AccessPathBase.LocalVar(resultRegister.index)))
            }
            is AccessPathBase.Argument -> {
                val idx = (factAp.base as AccessPathBase.Argument).idx
                if (isInvoke && idx == 0) {
                    val receiver = callInfo.receiver!!
                    val recvBase = GoFlowFunctionUtils.accessPathBase(receiver, method)
                        ?: return emptyList()
                    listOf(factAp.rebase(recvBase))
                } else {
                    val argIdx = idx - argOffset
                    if (argIdx >= 0 && argIdx < callInfo.args.size) {
                        val argBase = GoFlowFunctionUtils.accessPathBase(callInfo.args[argIdx], method)
                            ?: return emptyList()
                        listOf(factAp.rebase(argBase))
                    } else {
                        mapFreeVarArgToBinding(callInfo, method, factAp, idx, argOffset, rebase)
                    }
                }
            }
            is AccessPathBase.This -> error("This base is not used in Go")
            is AccessPathBase.ClassStatic -> listOf(factAp)
            is AccessPathBase.Constant -> listOf(factAp)
            else -> emptyList()
        }
    }

    // ── Call-to-Start (caller → callee) ──────────────────────────────

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
        onMappedFact: (FinalFactAp, AccessPathBase) -> Unit,
    ) {
        mapMethodCallToStartFlowAnyFact(callStatement, callExpr, returnValue, factAp, onMappedFact)
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        fact: InitialFactAp,
        onMappedFact: (InitialFactAp, AccessPathBase) -> Unit,
    ) {
        mapMethodCallToStartFlowAnyFact(callStatement, callExpr, returnValue, fact, onMappedFact)
    }

    fun <F: FactAp> mapMethodCallToStartFlowAnyFact(
        callStatement: CommonInst,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        factAp: F,
        onMappedFact: (F, AccessPathBase) -> Unit,
    ) {
        val goCallExpr = callExpr as GoCallExpr
        val callInfo = goCallExpr.callInfo
        val method = (callStatement as GoIRInst).location.functionBody.function
        val isInvoke = callInfo.receiver != null
        val argOffset = if (isInvoke) 1 else 0

        if (isInvoke) {
            val receiverBase = GoFlowFunctionUtils.accessPathBase(callInfo.receiver!!, method)
            if (receiverBase != null && factAp.base == receiverBase) {
                onMappedFact(factAp, AccessPathBase.Argument(0))
            }
        }

        for ((i, arg) in callInfo.args.withIndex()) {
            val argBase = GoFlowFunctionUtils.accessPathBase(arg, method)
            if (argBase != null && factAp.base == argBase) {
                val calleeBase = AccessPathBase.Argument(i + argOffset)
                onMappedFact(factAp, calleeBase)
            }
        }

        if (factAp.base is AccessPathBase.ClassStatic) {
            onMappedFact(factAp, AccessPathBase.ClassStatic)
        }

        mapClosureBindingsToStart(goCallExpr, method, factAp, onMappedFact)
    }

    // ── Closure binding helpers ──────────────────────────────────────

    private fun <F: FactAp> mapClosureBindingsToStart(
        goCallExpr: GoCallExpr,
        method: GoIRFunction,
        factAp: F,
        onMapped: (F, AccessPathBase) -> Unit,
    ) {
        val callInfo = goCallExpr.callInfo
        if (callInfo.mode != GoIRCallMode.DYNAMIC) return
        val enclosingMethod = goCallExpr.enclosingMethod

        val funcValue = callInfo.function as? GoIRRegister ?: return
        val closureExpr = GoFlowFunctionUtils.findMakeClosureExpr(funcValue, enclosingMethod) ?: return

        val paramCount = closureExpr.fn.params.size
        for ((i, binding) in closureExpr.bindings.withIndex()) {
            val bindingBase = GoFlowFunctionUtils.accessPathBase(binding, method)
            if (bindingBase != null && factAp.base == bindingBase) {
                val freeVarBase = AccessPathBase.Argument(paramCount + i)
                onMapped(factAp, freeVarBase)
            }
        }
    }

    // ── Free-var exit-to-return mapping ──────────────────────────────

    private fun <F: FactAp> mapFreeVarArgToBinding(
        callInfo: GoIRCallInfo,
        method: GoIRFunction,
        factAp: F,
        argIdx: Int,
        argOffset: Int,
        rebase: F.(AccessPathBase) -> F,
    ): List<F> {
        if (callInfo.mode != GoIRCallMode.DYNAMIC) return emptyList()
        val funcValue = callInfo.function as? GoIRRegister ?: return emptyList()
        val closureExpr = GoFlowFunctionUtils.findMakeClosureExpr(funcValue, method) ?: return emptyList()

        val freeVarIdx = argIdx - argOffset - callInfo.args.size
        if (freeVarIdx < 0 || freeVarIdx >= closureExpr.bindings.size) return emptyList()

        val bindingBase = GoFlowFunctionUtils.accessPathBase(closureExpr.bindings[freeVarIdx], method)
            ?: return emptyList()

        return listOf(factAp.rebase(bindingBase))
    }

    // ── Relevance and validity checks ────────────────────────────────

    override fun factIsRelevantToMethodCall(
        callStatement: CommonInst,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        factAp: FactAp,
    ): Boolean {
        val goCallExpr = callExpr as GoCallExpr
        val callInfo = goCallExpr.callInfo
        val method = (callStatement as GoIRInst).location.functionBody.function

        for (arg in callInfo.args) {
            val argBase = GoFlowFunctionUtils.accessPathBase(arg, method)
            if (argBase != null && argBase == factAp.base) return true
        }

        if (callInfo.receiver != null) {
            val recvBase = GoFlowFunctionUtils.accessPathBase(callInfo.receiver!!, method)
            if (recvBase != null && recvBase == factAp.base) return true
        }

        if (returnValue != null) {
            val retBase = GoFlowFunctionUtils.accessPathBase(returnValue as GoIRValue, method)
            if (retBase != null && retBase == factAp.base) return true
        }

        if (factAp.base is AccessPathBase.ClassStatic) return true

        // Check closure bindings for DYNAMIC calls
        if (callInfo.mode == GoIRCallMode.DYNAMIC) {
            val funcValue = callInfo.function as? GoIRRegister
            if (funcValue != null) {
                val closureExpr = GoFlowFunctionUtils.findMakeClosureExpr(funcValue, goCallExpr.enclosingMethod)
                if (closureExpr != null) {
                    for (binding in closureExpr.bindings) {
                        val bindingBase = GoFlowFunctionUtils.accessPathBase(binding, method)
                        if (bindingBase != null && bindingBase == factAp.base) return true
                    }
                }
            }
        }

        return false
    }

    override fun isValidMethodExitFact(factAp: FactAp): Boolean {
        return factAp.base !is AccessPathBase.LocalVar
    }
}

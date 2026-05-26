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
import org.opentaint.ir.go.value.GoIRFunctionValue
import org.opentaint.ir.go.value.GoIRRegister
import org.opentaint.ir.go.value.GoIRValue

object GoMethodCallFactMapper : MethodCallFactMapper {
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
        val callExpr = buildGoCallExpr(goInst, callInfo)
        val explicitArgs = callExpr.explicitArgs

        return when (factAp.base) {
            is AccessPathBase.Return -> {
                val resultRegister = GoFlowFunctionUtils.extractResultRegister(goInst)
                    ?: return emptyList()
                listOf(factAp.rebase(AccessPathBase.LocalVar(resultRegister.index)))
            }
            is AccessPathBase.Argument -> {
                val idx = (factAp.base as AccessPathBase.Argument).idx
                if (idx >= 0 && idx < explicitArgs.size) {
                    val argBase = GoFlowFunctionUtils.accessPathBase(explicitArgs[idx], method)
                        ?: return emptyList()
                    listOf(factAp.rebase(argBase))
                } else {
                    mapFreeVarArgToBinding(callExpr, method, factAp, idx, rebase)
                }
            }
            is AccessPathBase.This -> {
                val receiver = callExpr.effectiveReceiver ?: return emptyList()
                val recvBase = GoFlowFunctionUtils.accessPathBase(receiver, method)
                    ?: return emptyList()
                listOf(factAp.rebase(recvBase))
            }
            is AccessPathBase.ClassStatic -> listOf(factAp)
            is AccessPathBase.Constant -> listOf(factAp)
            else -> emptyList()
        }
    }

    /**
     * Re-build a [GoCallExpr] from a [GoIRInst] for the in-mapper paths that
     * receive only a [CommonInst]. Mirrors what [org.opentaint.dataflow.go.GoLanguageManager.getCallExpr]
     * does, including the DIRECT-method shape normalisation.
     */
    private fun buildGoCallExpr(goInst: GoIRInst, callInfo: GoIRCallInfo): GoCallExpr {
        val enclosingMethod = goInst.location.functionBody.function
        val callee = (callInfo.function as? GoIRFunctionValue)?.function
        return GoCallExpr(callInfo, callee, enclosingMethod)
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
        mapMethodCallToStartFlowAnyFact(callStatement, callExpr, factAp, onMappedFact)
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        fact: InitialFactAp,
        onMappedFact: (InitialFactAp, AccessPathBase) -> Unit,
    ) {
        mapMethodCallToStartFlowAnyFact(callStatement, callExpr, fact, onMappedFact)
    }

    fun <F: FactAp> mapMethodCallToStartFlowAnyFact(
        callStatement: CommonInst,
        callExpr: CommonCallExpr,
        factAp: F,
        onMappedFact: (F, AccessPathBase) -> Unit,
    ) {
        val goCallExpr = callExpr as GoCallExpr
        val method = (callStatement as GoIRInst).location.functionBody.function

        val receiver = goCallExpr.effectiveReceiver
        if (receiver != null) {
            val receiverBase = GoFlowFunctionUtils.accessPathBase(receiver, method)
            if (receiverBase != null && factAp.base == receiverBase) {
                onMappedFact(factAp, AccessPathBase.This)
            }
        }

        for ((i, arg) in goCallExpr.explicitArgs.withIndex()) {
            val argBase = GoFlowFunctionUtils.accessPathBase(arg, method)
            if (argBase != null && factAp.base == argBase) {
                onMappedFact(factAp, AccessPathBase.Argument(i))
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

        // For methods the receiver is `params[0]` and is materialised as
        // `AccessPathBase.This` (not an Argument), so free vars are indexed
        // starting from the count of *non-receiver* params.
        val paramCount = GoFlowFunctionUtils.nonReceiverParamCount(closureExpr.fn)
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
        callExpr: GoCallExpr,
        method: GoIRFunction,
        factAp: F,
        argIdx: Int,
        rebase: F.(AccessPathBase) -> F,
    ): List<F> {
        val callInfo = callExpr.callInfo
        if (callInfo.mode != GoIRCallMode.DYNAMIC) return emptyList()
        val funcValue = callInfo.function as? GoIRRegister ?: return emptyList()
        val closureExpr = GoFlowFunctionUtils.findMakeClosureExpr(funcValue, method) ?: return emptyList()

        val freeVarIdx = argIdx - callExpr.explicitArgs.size
        if (freeVarIdx < 0 || freeVarIdx >= closureExpr.bindings.size) return emptyList()

        val bindingBase = GoFlowFunctionUtils.accessPathBase(closureExpr.bindings[freeVarIdx], method)
            ?: return emptyList()

        return listOf(factAp.rebase(bindingBase))
    }

    override fun factIsRelevantToMethodCall(
        callStatement: CommonInst,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        factAp: FactAp,
    ): Boolean {
        val goCallExpr = callExpr as GoCallExpr
        val callInfo = goCallExpr.callInfo
        val method = (callStatement as GoIRInst).location.functionBody.function

        for (arg in goCallExpr.explicitArgs) {
            val argBase = GoFlowFunctionUtils.accessPathBase(arg, method)
            if (argBase != null && argBase == factAp.base) return true
        }

        val recv = goCallExpr.effectiveReceiver
        if (recv != null) {
            val recvBase = GoFlowFunctionUtils.accessPathBase(recv, method)
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

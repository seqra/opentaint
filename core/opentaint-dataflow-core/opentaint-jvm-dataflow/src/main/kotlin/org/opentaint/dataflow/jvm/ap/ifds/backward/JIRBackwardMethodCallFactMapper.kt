package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.analysis.MethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.JIRMethodCallFactMapper
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.jIRDowncast
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRCallExpr
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRInstanceCallExpr
import org.opentaint.ir.api.jvm.ext.cfg.callExpr
import org.opentaint.ir.api.jvm.ext.toType

object JIRBackwardMethodCallFactMapper : MethodCallFactMapper {
    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: FinalFactAp,
        checker: FactTypeChecker
    ): List<FinalFactAp> {
        jIRDowncast<JIRInst>(callStatement)
        return listOfNotNull(
            mapMethodExitToReturnFlowFact(
                callStatement, factAp,
                checkFactType = { type, f -> checker.filterFactByLocalType(type, f) },
                rebaseFact = { f, base -> f.rebase(base) }
            )
        )
    }

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: InitialFactAp
    ): List<InitialFactAp> {
        jIRDowncast<JIRInst>(callStatement)
        return listOfNotNull(
            mapMethodExitToReturnFlowFact(
                callStatement, factAp,
                checkFactType = { _, f -> f },
                rebaseFact = { f, base -> f.rebase(base) }
            )
        )
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        factAp: FinalFactAp,
        checker: FactTypeChecker,
        onMappedFact: (FinalFactAp, AccessPathBase) -> Unit
    ) {
        jIRDowncast<JIRMethod>(callee)
        jIRDowncast<JIRCallExpr>(callExpr)
        jIRDowncast<JIRImmediate?>(returnValue)
        mapMethodCallToStartFlowFact(
            callee, callExpr, returnValue, factAp,
            checkFactType = { type, f -> checker.filterFactByLocalType(type, f) },
            onMappedFact = onMappedFact
        )
    }

    override fun mapMethodCallToStartFlowFact(
        callStatement: CommonInst,
        callee: CommonMethod,
        callExpr: CommonCallExpr,
        returnValue: CommonValue?,
        fact: InitialFactAp,
        onMappedFact: (InitialFactAp, AccessPathBase) -> Unit
    ) {
        jIRDowncast<JIRMethod>(callee)
        jIRDowncast<JIRCallExpr>(callExpr)
        jIRDowncast<JIRImmediate?>(returnValue)
        mapMethodCallToStartFlowFact(
            callee, callExpr, returnValue, fact,
            checkFactType = { _, f -> f },
            onMappedFact = onMappedFact
        )
    }

    override fun factIsRelevantToMethodCall(
        callStatement: CommonInst,
        returnValue: CommonValue?,
        callExpr: CommonCallExpr,
        factAp: FactAp
    ): Boolean {
        jIRDowncast<JIRImmediate?>(returnValue)
        jIRDowncast<JIRCallExpr>(callExpr)
        return JIRMethodCallFactMapper.factIsRelevantToMethodCall(returnValue, callExpr, factAp.base)
    }

    override fun isValidMethodExitFact(factAp: FactAp): Boolean =
        isValidMethodExitFactBase(factAp.base)

    fun isValidMethodExitFactBase(base: AccessPathBase): Boolean = when (base) {
        is AccessPathBase.Argument,
        AccessPathBase.This,
        AccessPathBase.ClassStatic -> true

        else -> false
    }

    private inline fun <F : FactAp> mapMethodExitToReturnFlowFact(
        callStatement: JIRInst,
        factAp: F,
        checkFactType: (JIRType, F) -> F?,
        rebaseFact: (F, AccessPathBase) -> F,
    ): F? {
        val callExpr = callStatement.callExpr ?: error("Non call statement")

        return when (val base = factAp.base) {
            is AccessPathBase.ClassStatic,
            is AccessPathBase.Constant -> factAp

            is AccessPathBase.Argument -> {
                val argExpr = callExpr.args.getOrNull(base.idx) ?: return null
                val newBase = MethodFlowFunctionUtils.accessPathBase(argExpr) ?: return null
                if (newBase is AccessPathBase.Constant) return null

                val checkedFact = checkFactType(argExpr.type, factAp) ?: return null
                rebaseFact(checkedFact, newBase)
            }

            AccessPathBase.This -> {
                check(callExpr is JIRInstanceCallExpr) { "Non instance call with <this> argument" }

                val newBase = MethodFlowFunctionUtils.accessPathBase(callExpr.instance) ?: return null
                if (newBase is AccessPathBase.Constant) return null

                val checkedFact = checkFactType(callExpr.instance.type, factAp) ?: return null
                rebaseFact(checkedFact, newBase)
            }

            AccessPathBase.Return,
            AccessPathBase.Exception,
            is AccessPathBase.LocalVar -> null
        }
    }

    private inline fun <F : FactAp> mapMethodCallToStartFlowFact(
        callee: JIRMethod,
        callExpr: JIRCallExpr,
        returnValue: JIRImmediate?,
        factAp: F,
        checkFactType: (JIRType, F) -> F?,
        onMappedFact: (F, AccessPathBase) -> Unit,
    ) {
        val factBase = factAp.base

        if (returnValue != null && MethodFlowFunctionUtils.accessPathBase(returnValue) == factBase) {
            val checkedFact = checkFactType(returnValue.type, factAp)
            if (checkedFact != null) {
                onMappedFact(checkedFact, AccessPathBase.Return)
            }
            return
        }

        if (factBase is AccessPathBase.ClassStatic) {
            onMappedFact(factAp, factBase)
        }

        if (callExpr is JIRInstanceCallExpr) {
            val instanceBase = MethodFlowFunctionUtils.accessPathBase(callExpr.instance)
            if (instanceBase == factBase) {
                val checkedFact = checkFactType(callee.enclosingClass.toType(), factAp)
                if (checkedFact != null) {
                    onMappedFact(checkedFact, AccessPathBase.This)
                }
            }
        }

        for ((i, arg) in callExpr.args.withIndex()) {
            val argBase = MethodFlowFunctionUtils.accessPathBase(arg)
            if (argBase == factBase) {
                val checkedFact = checkFactType(arg.type, factAp)
                if (checkedFact != null) {
                    onMappedFact(checkedFact, AccessPathBase.Argument(i))
                }
            }
        }
    }
}

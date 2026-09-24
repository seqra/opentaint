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
import org.opentaint.ir.api.jvm.cfg.JIRImmediate

object JIRBackwardMethodCallFactMapper : MethodCallFactMapper by JIRMethodCallFactMapper {
    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: FinalFactAp,
        checker: FactTypeChecker
    ): List<FinalFactAp> {
        if (factAp.base == AccessPathBase.Return) return emptyList()
        return JIRMethodCallFactMapper.mapMethodExitToReturnFlowFact(callStatement, factAp, checker)
    }

    override fun mapMethodExitToReturnFlowFact(
        callStatement: CommonInst,
        factAp: InitialFactAp
    ): List<InitialFactAp> {
        if (factAp.base == AccessPathBase.Return) return emptyList()
        return JIRMethodCallFactMapper.mapMethodExitToReturnFlowFact(callStatement, factAp)
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
        val result = resultValue(returnValue, factAp)
        if (result != null) {
            checker.filterFactByLocalType(result.type, factAp)?.let { onMappedFact(it, AccessPathBase.Return) }
            return
        }

        JIRMethodCallFactMapper.mapMethodCallToStartFlowFact(
            callStatement, callee, callExpr, returnValue, factAp, checker, onMappedFact
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
        if (resultValue(returnValue, fact) != null) {
            onMappedFact(fact, AccessPathBase.Return)
            return
        }

        JIRMethodCallFactMapper.mapMethodCallToStartFlowFact(
            callStatement, callee, callExpr, returnValue, fact, onMappedFact
        )
    }

    override fun isValidMethodExitFact(factAp: FactAp): Boolean =
        isValidMethodExitFactBase(factAp.base)

    fun isValidMethodExitFactBase(base: AccessPathBase): Boolean = when (base) {
        is AccessPathBase.Argument,
        AccessPathBase.This,
        AccessPathBase.ClassStatic -> true

        else -> false
    }

    private fun resultValue(returnValue: CommonValue?, factAp: FactAp): JIRImmediate? {
        jIRDowncast<JIRImmediate?>(returnValue)
        return returnValue?.takeIf { MethodFlowFunctionUtils.accessPathBase(it) == factAp.base }
    }
}

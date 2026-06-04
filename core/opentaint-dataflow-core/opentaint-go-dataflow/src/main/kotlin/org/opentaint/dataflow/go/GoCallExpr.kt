package org.opentaint.dataflow.go

import org.opentaint.ir.api.common.cfg.CommonCallExpr
import org.opentaint.ir.api.common.cfg.CommonInstanceCallExpr
import org.opentaint.ir.api.common.cfg.CommonValue
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.cfg.GoIRCallTarget
import org.opentaint.ir.go.type.GoIRCallMode
import org.opentaint.ir.go.value.GoIRValue

open class GoCallExpr(
    val callInfo: GoIRCallInfo,
    val resolvedCallee: GoIRFunction?,
    val enclosingMethod: GoIRFunction,
) : CommonCallExpr {
    override val args: List<CommonValue>
        get() = explicitArgs.map { it as CommonValue }

    override val typeName: String
        get() = callInfo.resultType.displayName

    val effectiveReceiver: GoIRValue?
        get() = when {
            callInfo.receiver != null -> callInfo.receiver
            resolvedCallee?.isMethod == true -> callInfo.args.firstOrNull()
            else -> null
        }

    val explicitArgs: List<GoIRValue>
        get() = when {
            callInfo.receiver != null -> callInfo.args
            resolvedCallee?.isMethod == true -> callInfo.args.drop(1)
            else -> callInfo.args
        }

    val calleeName: String?
        get() {
            resolvedCallee?.fullName?.let { return it }
            val target = callInfo.target
            if (target is GoIRCallTarget.Builtin) return target.name
            if (callInfo.mode == GoIRCallMode.INVOKE) {
                val recvType = callInfo.receiver?.type?.displayName ?: return null
                val methodName = callInfo.methodName ?: return null
                return "($recvType).$methodName"
            }
            return null
        }
}

class GoInstanceCallExpr(
    callInfo: GoIRCallInfo,
    resolvedCallee: GoIRFunction?,
    override val instance: CommonValue,
    enclosingMethod: GoIRFunction,
) : GoCallExpr(callInfo, resolvedCallee, enclosingMethod), CommonInstanceCallExpr

fun GoCallExpr.signature(): GoFunctionSignature? {
    val name = calleeName ?: return null
    val receiverType = effectiveReceiver?.type
    val paramTypes = explicitArgs.map { it.type }
    val resultType = callInfo.resultType
    return GoFunctionSignature(name, receiverType, paramTypes, resultType)
}

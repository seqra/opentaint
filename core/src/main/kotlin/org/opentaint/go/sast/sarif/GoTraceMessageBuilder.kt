package org.opentaint.go.sast.sarif

import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.ir.go.cfg.GoIRCallInfo
import org.opentaint.ir.go.cfg.GoIRCallTarget
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.ir.go.type.GoIRCallMode
import org.opentaint.common.sast.sarif.TracePathNode
import org.opentaint.common.sast.sarif.TracePathNodeKind

/**
 * Go counterpart of [org.opentaint.jvm.sast.sarif.TraceMessageBuilder].
 *
 * Produces human-readable per-step trace messages mirroring the Java SARIF
 * message style, operating directly on Go IR instructions and call info.
 */
class GoTraceMessageBuilder(private val sinkMessage: String) {

    fun messageFor(node: TracePathNode): String = when (node.kind) {
        TracePathNodeKind.SOURCE -> calleeName(node)
            ?.let { "Tainted data produced by $it" } ?: "Tainted data produced here"
        TracePathNodeKind.SINK -> sinkMessage
        TracePathNodeKind.CALL -> calleeName(node)?.let { "Call to $it" } ?: "Call"
        TracePathNodeKind.RETURN -> calleeName(node)?.let { "Returning from $it" } ?: "Returning"
        TracePathNodeKind.OTHER -> "Taint propagates here"
    }

    fun sarifKind(node: TracePathNode): String = when (node.kind) {
        TracePathNodeKind.SOURCE, TracePathNodeKind.SINK -> "taint"
        TracePathNodeKind.CALL -> "call"
        TracePathNodeKind.RETURN -> "return"
        TracePathNodeKind.OTHER -> "unknown"
    }

    private fun calleeName(node: TracePathNode): String? {
        val inst = node.statement as? GoIRInst ?: return null
        val callInfo = GoFlowFunctionUtils.extractCallInfo(inst) ?: return null
        return calleeName(callInfo)
    }

    private fun calleeName(callInfo: GoIRCallInfo): String? {
        when (val target = callInfo.target) {
            is GoIRCallTarget.Function -> return shortName(target.function.fullName)
            is GoIRCallTarget.Builtin -> return target.name
            else -> {}
        }
        if (callInfo.mode == GoIRCallMode.INVOKE) {
            val method = callInfo.methodName ?: return null
            val recv = callInfo.receiver?.type?.displayName
            return if (recv != null) "$recv.$method" else method
        }
        return null
    }

    private fun shortName(fullName: String): String =
        fullName.substringAfterLast('.').ifEmpty { fullName }
}

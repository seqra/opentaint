package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.MethodContext
import org.opentaint.dataflow.ap.ifds.analysis.MethodEntrypointResolver
import org.opentaint.dataflow.jvm.ap.ifds.JIRLanguageManager
import org.opentaint.dataflow.jvm.ap.ifds.jIRDowncast
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.util.analysis.ApplicationGraph

class JIRBackwardMethodEntrypointResolver(
    private val backwardGraph: ApplicationGraph<CommonMethod, CommonInst>,
    private val languageManager: JIRLanguageManager,
) : MethodEntrypointResolver {
    override fun resolveEntryPoints(method: CommonMethod, context: MethodContext): List<JIRInst> {
        jIRDowncast<JIRMethod>(method)
        return backwardGraph.methodGraph(method).entryPoints()
            .filterNot { languageManager.producesExceptionalControlFlow(it) }
            .filterIsInstance<JIRInst>()
            .toList()
    }
}

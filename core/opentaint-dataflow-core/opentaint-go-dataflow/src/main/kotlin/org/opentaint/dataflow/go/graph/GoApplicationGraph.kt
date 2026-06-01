package org.opentaint.dataflow.go.graph

import mu.KLogging
import org.opentaint.dataflow.go.GoCallResolver
import org.opentaint.dataflow.go.GoFlowFunctionUtils
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.ir.go.api.GoIRBody
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.util.analysis.ApplicationGraph

class GoApplicationGraph(
    val cp: GoIRProgram,
    unitResolver: UnitResolver<GoIRFunction>,
) : ApplicationGraph<GoIRFunction, GoIRInst> {
    internal val callResolver = GoCallResolver(cp, unitResolver)

    override fun callees(node: GoIRInst): Sequence<GoIRFunction> {
        val callInfo = GoFlowFunctionUtils.extractCallInfo(node) ?: return emptySequence()
        return callResolver.resolve(callInfo, node).orEmpty().asSequence()
    }

    override fun callers(method: GoIRFunction): Sequence<GoIRInst> {
        // Scan all functions for call instructions that resolve to this method.
        // O(n) across all instructions — acceptable for MVP.
        return cp.allFunctions().asSequence()
            .filter { it.bodyAvailable }
            .mapNotNull { it.body }
            .flatMap { body ->
                body.instructions.asSequence().filter { inst ->
                    val callInfo = GoFlowFunctionUtils.extractCallInfo(inst)
                    callInfo != null && callResolver.resolve(callInfo, inst).orEmpty().any { it == method }
                }
            }
    }

    override fun methodOf(node: GoIRInst): GoIRFunction =
        node.location.functionBody.function

    override fun methodGraph(method: GoIRFunction): ApplicationGraph.MethodGraph<GoIRFunction, GoIRInst> {
        if (!method.bodyAvailable) {
            logger.error("Function ${method.fullName} body is not available")
            return GoErrorFunctionGraph(this, method)
        }

        val body = method.body
        if (body == null) {
            logger.error("Function ${method.fullName} has no body")
            return GoErrorFunctionGraph(this, method)
        }

        return GoFunctionGraph(this, method, body)
    }

    private class GoErrorFunctionGraph(
        override val applicationGraph: GoApplicationGraph,
        override val method: GoIRFunction,
    ) : ApplicationGraph.MethodGraph<GoIRFunction, GoIRInst> {
        override fun predecessors(node: GoIRInst): Sequence<GoIRInst> = emptySequence()
        override fun successors(node: GoIRInst): Sequence<GoIRInst> = emptySequence()
        override fun entryPoints(): Sequence<GoIRInst> = emptySequence()
        override fun exitPoints(): Sequence<GoIRInst> = emptySequence()
        override fun statements(): Sequence<GoIRInst> = emptySequence()
    }

    class GoFunctionGraph(
        override val applicationGraph: GoApplicationGraph,
        override val method: GoIRFunction,
        val body: GoIRBody
    ) : ApplicationGraph.MethodGraph<GoIRFunction, GoIRInst> {
        override fun predecessors(node: GoIRInst): Sequence<GoIRInst> =
            body.instGraph.predecessorsList(node).asSequence()

        override fun successors(node: GoIRInst): Sequence<GoIRInst> =
            body.instGraph.successorsList(node).asSequence()

        override fun entryPoints(): Sequence<GoIRInst> =
            body.instGraph.entries.asSequence()

        override fun exitPoints(): Sequence<GoIRInst> =
            body.instGraph.exits.asSequence()

        override fun statements(): Sequence<GoIRInst> =
            body.instructions.asSequence()
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}

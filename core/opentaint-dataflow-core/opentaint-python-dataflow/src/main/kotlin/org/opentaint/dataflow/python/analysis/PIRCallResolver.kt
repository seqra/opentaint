package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.*

/**
 * Resolves PIRCall instructions to concrete PIRFunction callees.
 *
 * Resolution order:
 *  1. mypy's static resolution via [PIRCall.resolvedCallee].
 *  2. Flow-sensitive name reconstruction from [PIRMethodQFNameReconstructor] — handles
 *     module-imported names, closures (`PIRBindFunctionExpr`), chained attribute
 *     access, and constructor-typed locals. Cached per method.
 */
class PIRCallResolver(
    private val cp: PIRClasspath,
    private val applicationGraph: PIRApplicationGraph,
) {

    private val perMethodNames: MutableMap<PIRFunction, Map<PIRInstruction, Set<String>>> = hashMapOf()

    private fun namesFor(method: PIRFunction): Map<PIRInstruction, Set<String>> =
        perMethodNames.getOrPut(method) {
            PIRMethodQFNameReconstructor.compute(method, applicationGraph)
        }

    fun resolve(call: PIRCall, method: PIRFunction): Set<PIRFunction> = buildSet {
        // 1. mypy's resolvedCallee. The proto-to-flat layer normalizes mypy's
        // lexical names (`m.outer.inner`) to the lifter's flat-encoded qualified
        // names (`m.outer$inner`) at module-build time, so a direct lookup
        // against the classpath qn registry succeeds for any fully-qualified
        // in-module callee.
        call.resolvedCallee?.let { cp.findFunctionOrNull(it)?.let(::add) }

        // 2. Flow-sensitive QN candidates from the reconstructor.
        namesFor(method)[call]?.forEach { cp.findFunctionOrNull(it)?.let(::add) }
    }
}

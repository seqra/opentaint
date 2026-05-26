package org.opentaint.dataflow.python.analysis

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.*
import org.opentaint.ir.impl.python.PIRUnknownFunction
import org.opentaint.ir.impl.python.PIRUnknownModule

/**
 * Resolves PIRCall instructions to concrete PIRFunction callees.
 *
 * All callee-name candidates — mypy's static `resolvedCallee`, names
 * reconstructed from receiver types / constructor-typed locals, names
 * propagated through `PIRReadName` / `PIRBindFunctionExpr` chains — are
 * produced by [PIRMethodQFNameReconstructor] in a single pass per
 * method. This class only translates those candidate qualified names
 * to `PIRFunction`s: real ones via [PIRClasspath.findFunctionOrNull],
 * or a synthetic [PIRUnknownFunction] when no PIR body exists. The
 * synthetic path lets taint rules keyed on stdlib / library FQNs
 * (`builtins.str.upper`, etc.) match calls whose callee has no body
 * loaded into the classpath.
 */
class PIRCallResolver(
    private val cp: PIRClasspath,
    private val applicationGraph: PIRApplicationGraph,
) {

    private val perMethodNames: MutableMap<PIRFunction, Map<PIRInstruction, Set<String>>> = hashMapOf()
    private val syntheticByName: MutableMap<String, PIRUnknownFunction> = hashMapOf()

    private fun namesFor(method: PIRFunction): Map<PIRInstruction, Set<String>> =
        perMethodNames.getOrPut(method) {
            PIRMethodQFNameReconstructor.compute(method, applicationGraph)
        }

    private fun namesFor(method: PIRFunction, call: PIRInstruction) =
        namesFor(method).getOrDefault(call, emptySet())

    fun resolveNames(loadAttr: PIRInstruction) = namesFor(loadAttr.location.method, loadAttr)

    fun resolveCall(call: PIRCall): Set<PIRFunction> =
        resolveNames(call).mapTo(hashSetOf()) {
            cp.findFunctionOrNull(it)
                ?: syntheticFor(it)
        }

    private fun syntheticFor(qualifiedName: String): PIRUnknownFunction =
        syntheticByName.getOrPut(qualifiedName) {
            PIRUnknownFunction(
                name = qualifiedName.substringAfterLast('.'),
                qualifiedName = qualifiedName,
                module = PIRUnknownModule(qualifiedName.substringBeforeLast('.', ""), emptyList()),
            )
        }
}

package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.dataflow.python.graph.PIRQualifiedUnknownFunction
import org.opentaint.dataflow.python.graph.PIRSimpleNameUnknownFunction
import org.opentaint.dataflow.python.graph.StrippedCallArg
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.impl.python.PIRUnknownModule

/**
 * Resolves PIRCall instructions to concrete PIRFunction callees.
 *
 * Two reconstruction passes feed the resolver, in precedence order:
 *
 * 1. [PIRMethodQFNameReconstructor] produces fully-qualified callee names —
 *    mypy's static `resolvedCallee`, names reconstructed from receiver
 *    types / constructor-typed locals, names propagated through
 *    `PIRReadName` / `PIRBindFunctionExpr` chains.
 * 2. [PIRMethodSimpleNameReconstructor] is consulted only when (1) produces
 *    nothing for the call; it yields the trailing attribute segment of the
 *    callee operand (the "simple name"), so taint rules keyed on a bare
 *    method name can still match calls whose receiver chain couldn't be
 *    resolved to a global.
 *
 * Candidate names are translated to PIRFunctions: real ones via
 * [org.opentaint.ir.api.python.PIRClasspath.findFunctionOrNull], or a synthetic [org.opentaint.dataflow.python.graph.PIRUnknownFunction]
 * when no PIR body exists. The synthetic path lets taint rules keyed on
 * stdlib / library FQNs (`builtins.str.upper`, etc.) match calls whose
 * callee has no body loaded into the classpath. Qualified and simple-name
 * unknowns are split into [org.opentaint.dataflow.python.graph.PIRQualifiedUnknownFunction] /
 * [org.opentaint.dataflow.python.graph.PIRSimpleNameUnknownFunction] so downstream consumers can distinguish
 * the two precision levels at the type level.
 */
class PIRCallResolver(
    private val cp: PIRClasspath,
    private val applicationGraph: PIRApplicationGraph,
) {

    private val perMethodNames: MutableMap<PIRFunction, Map<PIRInstruction, Set<String>>> = hashMapOf()
    private val perMethodSimpleNames: MutableMap<PIRFunction, Map<PIRCall, Set<String>>> = hashMapOf()
    private val qualifiedSyntheticByName: MutableMap<Pair<String, List<StrippedCallArg>>, PIRQualifiedUnknownFunction> = hashMapOf()
    private val simpleNameSyntheticByName: MutableMap<Pair<String, List<StrippedCallArg>>, PIRSimpleNameUnknownFunction> = hashMapOf()

    private fun namesFor(method: PIRFunction): Map<PIRInstruction, Set<String>> =
        perMethodNames.getOrPut(method) {
            PIRMethodQFNameReconstructor.compute(method, applicationGraph)
        }

    private fun namesFor(method: PIRFunction, call: PIRInstruction) =
        namesFor(method).getOrDefault(call, emptySet())

    fun resolveNames(loadAttr: PIRInstruction) = namesFor(loadAttr.location.method, loadAttr)

    private fun simpleNamesFor(call: PIRCall): Set<String> {
        val method = call.location.method
        return perMethodSimpleNames
            .getOrPut(method) { PIRMethodSimpleNameReconstructor.compute(method, applicationGraph) }
            .getOrDefault(call, emptySet())
    }

    fun resolveCall(call: PIRCall): Set<PIRFunction> {
        val qfNames = resolveNames(call)
        if (qfNames.isNotEmpty()) {
            return qfNames.mapTo(hashSetOf()) {
                cp.findFunctionOrNull(it) ?: qualifiedSyntheticFor(it, call)
            }
        }
        return simpleNamesFor(call).mapTo(hashSetOf()) {
            cp.findFunctionOrNull(it) ?: simpleNameSyntheticFor(it, call)
        }
    }

    private fun qualifiedSyntheticFor(qualifiedName: String, call: PIRCall): PIRQualifiedUnknownFunction {
        val shape = call.args.map { StrippedCallArg(it.kind, it.keyword) }
        return qualifiedSyntheticByName.getOrPut(qualifiedName to shape) {
            PIRQualifiedUnknownFunction(qualifiedName, shape)
        }
    }

    private fun simpleNameSyntheticFor(name: String, call: PIRCall): PIRSimpleNameUnknownFunction {
        val shape = call.args.map { StrippedCallArg(it.kind, it.keyword) }
        return simpleNameSyntheticByName.getOrPut(name to shape) {
            PIRSimpleNameUnknownFunction(name, shape)
        }
    }
}
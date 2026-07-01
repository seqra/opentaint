package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.dataflow.python.graph.PIRQualifiedUnknownFunction
import org.opentaint.dataflow.python.graph.PIRSimpleNameUnknownFunction
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRLoadAttr

/**
 * Resolves PIRCall instructions to concrete PIRFunction callees.
 *
 * Two reconstruction passes feed the resolver, in precedence order:
 *
 * 1. [PIRMethodQFNameReconstructor] produces fully-qualified callee names —
 *    mypy's static `resolvedCallee`, names reconstructed from receiver
 *    types / constructor-typed locals, names propagated through
 *    `PIRReadNameExpr` / `PIRBindFunctionExpr` chains.
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
    private val qualifiedSyntheticByName: MutableMap<String, PIRQualifiedUnknownFunction> = hashMapOf()
    private val simpleNameSyntheticByName: MutableMap<String, PIRSimpleNameUnknownFunction> = hashMapOf()

    private fun namesFor(method: PIRFunction): Map<PIRInstruction, Set<String>> =
        perMethodNames.getOrPut(method) {
            PIRMethodQFNameReconstructor.compute(method, applicationGraph)
        }

    private fun simpleNamesFor(method: PIRFunction): Map<PIRCall, Set<String>> =
        perMethodSimpleNames.getOrPut(method) {
            PIRMethodSimpleNameReconstructor.compute(method, applicationGraph)
        }

    private fun resolveNames(inst: PIRInstruction): Set<String> {
        val method = inst.location.method
        return namesFor(method).getOrDefault(inst, emptySet())
    }

    private fun resolveSimpleNames(call: PIRInstruction): Set<String> {
        val method = call.location.method
        return simpleNamesFor(method).getOrDefault(call, emptySet())
    }

    fun resolveAttribute(inst: PIRLoadAttr): Set<String> {
        val qfNames = resolveNames(inst)
        if (qfNames.isNotEmpty()) return qfNames

        return setOf(inst.attribute)
    }

    fun resolveCall(call: PIRCall): Set<PIRFunction> {
        val qfNames = resolveNames(call)
        if (qfNames.isNotEmpty()) {
            return qfNames.mapTo(hashSetOf()) {
                cp.findFunctionOrNull(it) ?: qualifiedSyntheticFor(it)
            }
        }
        return resolveSimpleNames(call).mapTo(hashSetOf()) {
            cp.findFunctionOrNull(it) ?: simpleNameSyntheticFor(it)
        }
    }

    private fun qualifiedSyntheticFor(qualifiedName: String): PIRQualifiedUnknownFunction =
        qualifiedSyntheticByName.getOrPut(qualifiedName) {
            PIRQualifiedUnknownFunction(qualifiedName)
        }

    private fun simpleNameSyntheticFor(name: String): PIRSimpleNameUnknownFunction =
        simpleNameSyntheticByName.getOrPut(name) { PIRSimpleNameUnknownFunction(name) }
}
package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.PIRAssign
import org.opentaint.ir.api.python.PIRCall
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction
import org.opentaint.ir.api.python.PIRLoadAttr
import org.opentaint.ir.api.python.PIRLocal
import org.opentaint.ir.api.python.targets

/**
 * Computes a "simple name" (the trailing attribute segment) for each
 * [org.opentaint.ir.api.python.PIRCall] in a method, as a fallback for [PIRMethodQFNameReconstructor].
 *
 * `obj.foo.bar(...)` yields `"bar"`; `foo(...)` where `foo` was bound by a
 * `PIRReadNameExpr` yields the last dotted segment of that read-name.
 *
 * Structurally mirrors [PIRMethodQFNameReconstructor] — the shared
 * worklist/CFG machinery lives in [PIRMethodIntraproceduralWalker]. The
 * binding payload here is just `(localIdx, simpleName)`, with no segment
 * tree and no parameter-reference failure mode: a simple name is whatever
 * we last attached to a local, propagated through copy-assigns and dropped
 * on reassignment.
 */
class PIRMethodSimpleNameReconstructor private constructor(
    method: PIRFunction,
    applicationGraph: PIRApplicationGraph,
) : PIRMethodIntraproceduralWalker<PIRMethodSimpleNameReconstructor.LocalBinding>(method, applicationGraph) {

    private val result = mutableMapOf<PIRCall, MutableSet<String>>()

    private fun compute(): Map<PIRCall, Set<String>> {
        walk()
        return result
    }

    // Only PIRLoadAttr seeds bindings here. A PIRReadNameExpr-rooted callee always
    // yields a PIRMethodQFNameReconstructor result (the read produces a
    // GlobalRef binding that flattens), so the simple-name fallback is never
    // consulted for those calls.
    override fun initialBinding(inst: PIRInstruction): LocalBinding? = when (inst) {
        is PIRLoadAttr -> LocalBinding(inst.target.index, inst.attribute)
        else -> null
    }

    override fun transfer(inst: PIRInstruction, payload: LocalBinding): List<LocalBinding> = buildList {
        val idx = payload.idx

        when (inst) {
            is PIRCall -> {
                val calleeIdx = (inst.callee as? PIRLocal)?.index
                val targetIdx = inst.target?.index

                if (calleeIdx == idx) {
                    result.getOrPut(inst) { hashSetOf() }.add(payload.name)
                }

                if (targetIdx != idx) {
                    this += payload
                }
            }

            is PIRAssign -> {
                val sourceIdx = (inst.expr as? PIRLocal)?.index
                val targetIdx = inst.target.index

                if (idx != targetIdx) {
                    this += payload
                }

                if (sourceIdx == idx) {
                    this += LocalBinding(targetIdx, payload.name)
                }
            }

            else -> {
                val idxReassignment = inst.targets.any { it.index == idx }

                if (!idxReassignment) {
                    this += payload
                }
            }
        }
    }

    data class LocalBinding(val idx: Int, val name: String)

    companion object {
        fun compute(method: PIRFunction, applicationGraph: PIRApplicationGraph): Map<PIRCall, Set<String>> =
            PIRMethodSimpleNameReconstructor(method, applicationGraph).compute()
    }
}
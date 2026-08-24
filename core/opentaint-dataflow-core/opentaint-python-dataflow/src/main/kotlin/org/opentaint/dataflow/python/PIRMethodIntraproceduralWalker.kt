package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction

abstract class PIRMethodIntraproceduralWalker<B : Any>(
    method: PIRFunction,
    applicationGraph: PIRApplicationGraph,
) {
    protected val graph = applicationGraph.methodGraph(method)

    private val queue = mutableListOf<Pair<PIRInstruction, B>>()
    private val storage = MutableList(method.instList.size) { hashSetOf<B>() }

    protected fun walk() {
        for (inst in graph.statements()) {
            val seed = initialBinding(inst) ?: continue
            propagateToSuccessors(inst, seed)
        }
        while (queue.isNotEmpty()) {
            val (inst, payload) = queue.removeLast()
            transfer(inst, payload).forEach { propagateToSuccessors(inst, it) }
        }
    }

    protected abstract fun initialBinding(inst: PIRInstruction): B?

    protected abstract fun transfer(inst: PIRInstruction, payload: B): List<B>

    private fun propagateToSuccessors(inst: PIRInstruction, payload: B) {
        graph.successors(inst).forEach { addEntry(it, payload) }
    }

    private fun addEntry(inst: PIRInstruction, payload: B) {
        if (storage[inst.location.index].add(payload)) {
            queue += inst to payload
        }
    }
}

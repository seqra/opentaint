package org.opentaint.dataflow.python

import org.opentaint.dataflow.python.graph.PIRApplicationGraph
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRInstruction

/**
 * Forward intraprocedural worklist walker over a PIR method's CFG.
 *
 * Subclasses choose a payload type [B] and supply two transfer functions:
 *
 * - [initialBinding] is called once per reachable statement during
 *   seeding. It returns the binding the instruction emits *from itself*,
 *   with no incoming payload, or `null` if it emits nothing.
 * - [transfer] is called each time an instruction is reached with an
 *   incoming payload. It returns zero or more payloads to propagate to
 *   the instruction's successors.
 *
 * In both cases the returned bindings are propagated to the instruction's
 * **successors**, not back to the instruction itself.
 *
 * The walker handles seeding, the worklist, per-instruction dedup of
 * `(instruction, payload)` pairs, and successor propagation via
 * `graph.successors`. Result collection is the subclass's responsibility —
 * `initialBinding` / `transfer` are free to record findings as a side
 * effect.
 *
 * [B] must have value-based equality so dedup works (typically a data
 * class).
 */
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
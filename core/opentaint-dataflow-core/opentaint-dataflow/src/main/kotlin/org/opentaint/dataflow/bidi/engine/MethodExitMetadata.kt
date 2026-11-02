package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.ExitRules

/** DATA-only method metadata. Rule evaluation and its joins belong to the actual leaf. */
internal fun finishMethodData(ops: ApOps, mode: ApMode, original: PremiseKey,
                              value: Facts, exit: ExitRules, actualParts: List<Facts>? = null): Facts? {
    var result: Facts? = value
    if (mode.direction == Direction.FORWARD && exit.globalStateDrop && original.isZero && value.base == STATIC) {
        // Preserve the existing ordered positive-check projection. Every part
        // is selected from the original input, before any subtraction happens.
        val parts = actualParts ?: ArrayList<Facts>().also { selected ->
        for (sink in exit.rules.sinks) {
            ops.manager.cancellation.checkpoint()
            fun select(pattern: Pattern) {
                val checked = ops.checkMark(value, pattern, mode, null)
                if (checked is MarkCheck.Holds) selected += checked.facts
            }
            val predicate = sink.predicate
            if (predicate != null && !predicate.isTrue) when (value) {
                is FlowTree -> predicate.matchingLeaves(value.base, null) { _, literal -> select(literal) }
                is Reach -> predicate.matchingLeaves(value.base, TaintMark.ZERO) { _, literal -> select(literal) }
                is TaintTree -> {
                    val leaves = ops.manager.taintAlg.foldAll(value.root, ops.manager.cancellation)
                    for (mark in (leaves.exact + leaves.any).data)
                        predicate.matchingLeaves(value.base, TaintMark(mark)) { _, literal -> select(literal) }
                }
            } else for (literal in sink.patterns) select(literal)
        }
        }
        for (part in parts) {
            ops.manager.cancellation.checkpoint()
            result = result?.let { ops.without(it, part) }
        }
    }
    if (!mode.run1 && original.isZero && value is TaintTree)
        exit.entryMarkRemoval(value.base)?.let { marks -> result = result?.let { ops.withoutMarks(it, marks) } }
    return result
}

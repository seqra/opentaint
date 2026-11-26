package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*

/**
 * Forward-run capture trees (spec backward-condition-progress §I.3). The driver reads them at the barrier, as
 * [SourceHitStore]. One writer owns this store: the root analyzer of a method and its blocks.
 */
class CaptureTreeStore(private val ap: ApManager) {
    private val sinks = HashMap<CaptureKey, TaintNode>()
    private val sources = HashMap<CaptureKey, TaintNode>()

    fun addSink(key: CaptureKey, input: Facts?) = add(sinks, key, input)
    fun addSource(key: CaptureKey, input: Facts?) = add(sources, key, input)

    private fun add(trees: HashMap<CaptureKey, TaintNode>, key: CaptureKey, input: Facts?) {
        if (input !is TaintTree || !captured(key.literal)) return         // a FLOW fact never satisfies a literal (F4)
        val old = trees[key]
        val new = ap.captureInput(old, input, key.literal) ?: return
        if (new !== old) trees[key] = new
    }

    /** Only `[any]` literals with an empty exclusion and a FULL concrete mark (C7). */
    private fun captured(p: Pattern): Boolean = p.fact.tail == Tail.ANY && p.exclusion == ExclusionSet.Empty &&
        (p.fact.mark as? MarkSlot.Concrete)?.mark?.let { !ap.marks.isGroup(it) } == true

    fun sinkTrees(): Map<CaptureKey, TaintNode> = sinks
    fun sourceTrees(): Map<CaptureKey, TaintNode> = sources
}

package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.Facts
import org.opentaint.dataflow.bidi.ap.PremiseKey
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.util.SoftReferenceManager
import java.lang.ref.Reference

/** P2': the loop-output restrictions of one method runtime in one run.
 *
 * In one run, the restriction of an applied value reads only frozen run inputs (the demand scope views,
 * the records, the saved targets, the layout, the live locals, the end rules) and pure caches. So it is
 * a function of [Key] (spec/next-iteration-p1-p3.md §3.6; Lean `ApSpec.RestrictionMemoImpl`). A miss
 * computes the restriction, so a cleared memo is still exact. The method actor owns the memo: it is
 * not thread-safe. */
internal class LoopRestrictionMemo(
    private val refs: SoftReferenceManager,
    private val maxEntries: Int = MAX_ENTRIES,
) {
    data class Key(val parent: BlockScope, val loop: BlockId, val exit: PortId,
                   val original: PremiseKey, val value: Facts)

    private var entries: Reference<HashMap<Key, List<Facts>>>? = null

    fun getOrCompute(key: Key, compute: () -> List<Facts>): List<Facts> {
        entries?.get()?.get(key)?.let { return it }
        val values = compute()
        val map = entries?.get() ?: HashMap<Key, List<Facts>>().also { fresh ->
            entries = refs.createRef(fresh) ?: return values       // the memory guard is active: keep nothing
        }
        if (map.size >= maxEntries) map.clear()
        map[key] = values
        return values
    }

    fun clear() { entries?.clear(); entries = null }

    companion object { const val MAX_ENTRIES = 1_000_000 }
}

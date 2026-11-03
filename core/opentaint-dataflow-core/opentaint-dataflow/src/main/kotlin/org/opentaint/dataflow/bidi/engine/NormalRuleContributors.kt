package org.opentaint.dataflow.bidi.engine

import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.ResumeSite
import org.opentaint.dataflow.bidi.store.*

/** One actor-owned condition cache facade. Only an accepted current leaf may
 * activate [restoreOnce]. It never schedules facts, actions, or initials. */
class NormalRuleContributors(
    private val manager: ApManager,
    previous: NormalRuleContributorView,
    method: MethodKey,
    scope: BlockScope,
    mode: ApMode,
) {
    private val enabled = mode.direction == Direction.FORWARD && mode.markMode == MarkMode.FULL
    private val owner = NormalRuleContributorOwner(method, scope, mode.markMode, mode.direction)
    private var previous: NormalRuleContributorView? = if (enabled) previous else null
    private var restored: MutableSet<NormalRuleContributorKey>? = if (enabled) HashSet() else null
    private var temporary: NormalRuleContributorStore? = if (enabled) NormalRuleContributorStore(manager) else null
    private var frozen = false
    var capturedRows: Long = 0; private set
    var capturedUpdates: Long = 0; private set
    var restoredRows: Long = 0; private set

    /** The callback inserts old leaves into the ordinary join and collects ready
     * complete bindings. Its caller drains those bindings before the new input. */
    fun restoreOnce(rule: NormalRuleDescriptor, site: ResumeSite,
                    replay: (NormalRuleContributorRow) -> Unit): Boolean {
        check(!frozen) { "Condition contributors were frozen" }
        if (!enabled) return false
        manager.cancellation.checkpoint()
        val key = key(rule, site)
        if (!checkNotNull(restored).add(key)) return false
        for (row in checkNotNull(previous).rows(key)) {
            manager.cancellation.checkpoint()
            replay(row)
            restoredRows++
        }
        return true
    }

    fun keep(rule: NormalRuleDescriptor, site: ResumeSite, leaf: Int, input: ConjunctionStore.Input): Boolean {
        check(!frozen) { "Condition contributors were frozen" }
        if (!enabled || input.layer != Layer.NORMAL || input.facts?.layer != Layer.NORMAL) return false
        val temporary = checkNotNull(temporary)
        val count = temporary.retainedRows
        val fresh = temporary.publish(listOf(NormalRuleContributorRow(key(rule, site), leaf, input)))
        capturedRows += temporary.retainedRows - count
        if (fresh && temporary.retainedRows == count) capturedUpdates++
        return fresh
    }

    /** Snapshot cleanup has no cancellation point; a failed run exports nothing
     * at its barrier, but still releases reader and deduplication references. */
    fun freezeRows(): List<NormalRuleContributorRow> {
        check(!frozen) { "Condition contributors were already frozen" }
        return try { temporary?.snapshot()?.allRows().orEmpty() }
        finally {
            previous = null
            restored?.clear(); restored = null
            temporary = null
            frozen = true
        }
    }

    private fun key(rule: NormalRuleDescriptor, site: ResumeSite) =
        NormalRuleContributorKey(owner, rule, stableSite(rule, site))

    companion object {
        fun stableSite(rule: NormalRuleDescriptor, site: ResumeSite): NormalRuleSite = NormalRuleSite.of(rule, site)
    }
}

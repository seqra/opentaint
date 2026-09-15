package org.opentaint.dataflow.util

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.SideEffectKind
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicLong

/** Identity of one re-post: the method it leaves, the fact it arrived on, the kind it carries. */
data class ClimbKey(
    val method: MethodEntryPoint,
    val incomingFact: InitialFactAp,
    val kind: SideEffectKind,
)

/**
 * PROTOTYPE bound on the taint-mark field-unfold request "climb".
 *
 * When a sink condition needs a taint mark that is hidden under a parameter's `[any]`
 * abstraction, [org.opentaint.dataflow.taint.TaintMarkFieldUnfoldRequest] is posted as a
 * side effect. If a caller's refinement delta does not contain the mark, the request is
 * re-posted to that caller's own callers. Nothing bounds that climb: the re-posted fact is
 * the caller's fact (one access step longer each hop) with its exclusions erased, so in a
 * recursive method the fact grows without bound. Each re-post also pays a whole-tree
 * re-abstraction in `MethodAnalyzer.handleInputFactChange`, which is what collapses
 * throughput.
 *
 * Two independent levers, both switchable at runtime so a single jar can be swept:
 *  - [memoEnabled]  drop a re-post whose (method, incoming fact, outgoing kind) was already posted.
 *  - [maxDepth]     refuse to re-post once the outgoing fact is deeper than this.
 *  - [disabled]     skip the override entirely, i.e. behave like MethodSideEffectSummaryHandler.
 */
object UnfoldClimbBound {
    /** Behave exactly like the default `MethodSideEffectSummaryHandler.handleFactToFact`. */
    val disabled: Boolean =
        System.getProperty("opentaint.unfoldClimb.disable")?.toBooleanStrictOrNull() ?: false

    /** Drop exact-duplicate re-posts. */
    val memoEnabled: Boolean =
        System.getProperty("opentaint.unfoldClimb.memo")?.toBooleanStrictOrNull() ?: true

    /** Maximum depth of a re-posted fact; -1 disables the bound. */
    val maxDepth: Int =
        System.getProperty("opentaint.unfoldClimb.maxDepth")?.toIntOrNull() ?: -1

    /** Include the caller-supplied `suffix` in the request's identity (the f24ea78d3 behaviour). */
    val suffixInKey: Boolean =
        System.getProperty("opentaint.unfoldClimb.suffixInKey")?.toBooleanStrictOrNull() ?: false

    /** Only act on a request while it is still the bare abstraction (the 8867fb730 guard). */
    val unrefinedOnly: Boolean =
        System.getProperty("opentaint.unfoldClimb.unrefinedOnly")?.toBooleanStrictOrNull() ?: false

    val droppedByRefined = AtomicLong()

    val statsEnabled: Boolean =
        System.getProperty("opentaint.unfoldClimb.stats")?.toBooleanStrictOrNull() ?: true

    private val seen = ConcurrentHashMap.newKeySet<Any>()

    val reposted = AtomicLong()
    val droppedByMemo = AtomicLong()
    val droppedByDepth = AtomicLong()
    val answeredLocally = AtomicLong()
    val maxDepthSeen = AtomicLong()

    /** @return true when this re-post is a duplicate and should be dropped. */
    fun isDuplicate(key: Any): Boolean = memoEnabled && !seen.add(key)

    fun exceedsDepth(depth: Int): Boolean = maxDepth >= 0 && depth > maxDepth

    fun noteDepth(depth: Int) {
        if (!statsEnabled) return
        maxDepthSeen.updateAndGet { if (depth > it) depth.toLong() else it }
    }

    init {
        if (statsEnabled) {
            Runtime.getRuntime().addShutdownHook(Thread { System.err.println(report()) })
        }
    }

    fun report(): String = buildString {
        append("unfoldClimb: disabled=").append(disabled)
        append(" memo=").append(memoEnabled)
        append(" maxDepth=").append(maxDepth)
        append(" suffixInKey=").append(suffixInKey)
        append(" unrefinedOnly=").append(unrefinedOnly)
        append(" | answeredLocally=").append(answeredLocally.get())
        append(" reposted=").append(reposted.get())
        append(" droppedByMemo=").append(droppedByMemo.get())
        append(" droppedByDepth=").append(droppedByDepth.get())
        append(" droppedByRefined=").append(droppedByRefined.get())
        append(" distinctKeys=").append(seen.size)
        append(" maxFactDepth=").append(maxDepthSeen.get())
    }
}

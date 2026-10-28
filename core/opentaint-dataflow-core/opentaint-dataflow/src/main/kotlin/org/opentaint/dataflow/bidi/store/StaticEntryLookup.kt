package org.opentaint.dataflow.bidi.store

import org.opentaint.dataflow.bidi.ap.*

/** C2 needs a marked output witness, not all its source/mark products. */
internal class StaticEntryLookup(
    private val ap: ApManager,
    private val method: MethodKey,
    private val completion: FrozenCompletion,
    private val actual: List<Pattern>,
    private val out: InitialDemandResults,
    private val stats: DemandQueryStatistics?,
) {
    private fun joins(output: Pattern, input: Pattern): Boolean {
        stats?.add(6)
        return staticAnchor(ap, output) == staticAnchor(ap, input) && overlap(output, input)
    }
    fun directLocal() {
        val view = completion.local(method)
        for (leaf in actual) for (entry in view.entries(leaf)) {
            ap.cancellation.checkpoint()
            out.offer(entry, leaf)
        }
    }

    /** Remote search starts afresh. No local visited bit can hide remote adjacency. */
    fun search(visible: Boolean, covered: () -> Boolean) {
        stats?.add(if (visible) 2 else 1)
        val view = if (visible) completion.visible(method) else completion.local(method)
        for (leaf in actual) {
            ap.cancellation.checkpoint()
            // Abstract ordinary inputs cannot acquire a mark from a static path.
            if (leaf.fact.base != STATIC && leaf.fact.mark is MarkSlot.Star) continue
            for (entry in view.entries(leaf)) out.offer(entry, leaf)
            if (covered()) return
            val mark = (leaf.fact.mark as? MarkSlot.Concrete)?.mark ?: continue
            if (mark == TaintMark.ZERO) continue
            for (rightmost in view.flowTargets(leaf)) {
                ap.cancellation.checkpoint()
                if (rightmost.from.fact.base == STATIC) {
                    val colored = rightmost.to.copy(fact = rightmost.to.fact.copy(mark = MarkSlot.Concrete(mark)))
                    if (!out.has(colored, leaf) && exists(view, rightmost.from, mark)) out.offer(colored, leaf)
                }
                if (covered()) return
            }
        }
    }

    /** Forward states are outputs, backward states are inputs. Meetings are directed joins. */
    private fun exists(view: StaticDemandView, input: Pattern, mark: TaintMark): Boolean {
        val forward = ArrayDeque<Pattern>()
        val backward = ArrayDeque<Pattern>()
        val seenForward = HashSet<Pattern>()
        val seenBackward = HashSet<Pattern>()
        val forwardLocations = PathTrie<Pattern>(ap.cancellation)
        val backwardLocations = PathTrie<Pattern>(ap.cancellation)
        fun geometry(p: Pattern): Pattern = p.copy(fact = p.fact.copy(mark = MarkSlot.STAR))
        fun admit(p: Pattern, isForward: Boolean): Boolean {
            val value = geometry(p)
            val seen = if (isForward) seenForward else seenBackward
            if (!seen.add(value)) return false
            stats?.add(5)
            val opposite = if (isForward) backwardLocations else forwardLocations
            var meeting = false
            opposite.visitAroundWhile(STATIC, value.fact.path.toIntArray()) { other ->
                meeting = if (isForward) joins(value, other) else joins(other, value)
                !meeting
            }
            if (meeting) return true
            (if (isForward) forward else backward).addLast(value)
            (if (isForward) forwardLocations else backwardLocations).add(STATIC, value.fact.path.toIntArray(), value)
            return false
        }
        admit(input, false)
        // A location probe can answer before enumerating producers of this mark elsewhere.
        if (view.hasMarkedOutput(input, mark)) return true
        val roots = view.markedOutputs(mark).iterator()
        var rootsOpen = true
        var estimatedRoots = view.estimatedMarkedOutputs(mark)
        while (rootsOpen || forward.isNotEmpty() || backward.isNotEmpty()) {
            ap.cancellation.checkpoint()
            // Count unexamined roots as forward work when choosing the smaller frontier.
            val forwardWork = forward.size.toLong() + if (rootsOpen) estimatedRoots else 0
            val chooseBackward = backward.isNotEmpty() &&
                (forwardWork == 0L || backward.size.toLong() <= forwardWork)
            if (chooseBackward) {
                val at = backward.removeFirst()
                if (view.hasMarkedOutput(at, mark)) return true
                for (row in view.incoming(at, flowOnly = true))
                    if (joins(row.to, at) && admit(row.from, false)) return true
            } else {
                if (rootsOpen) {
                    if (roots.hasNext()) {
                        estimatedRoots = maxOf(0, estimatedRoots - 1)
                        stats?.add(4)
                        if (admit(roots.next(), true)) return true
                    } else { rootsOpen = false; estimatedRoots = 0 }
                }
                if (forward.isNotEmpty()) {
                    val output = forward.removeFirst()
                    for (row in view.outgoing(output)) if (joins(output, row.from) && admit(row.to, true)) return true
                }
            }
        }
        // Exhaust every eligible producer and both closures before a negative answer.
        return false
    }
}

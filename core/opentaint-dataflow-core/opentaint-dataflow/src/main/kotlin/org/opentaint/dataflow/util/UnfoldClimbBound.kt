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

    /**
     * First-wins memo on the QUESTION -- (frame, origin method, origin fact, mark) -- dropping the
     * summary-application detail (refinement kind, delta, suffix) from the request's identity.
     *
     * Minimisation on the depth ladder shows the engine asks each question 1 + k times, that only
     * the first asking carries it, and that the other k cannot even substitute for it: they are
     * causally downstream re-presentations. Required = 2d + 2, raised = 7d - 1.
     */
    @Volatile
    var questionMemo: Boolean =
        System.getProperty("opentaint.unfoldClimb.questionMemo")?.toBooleanStrictOrNull() ?: false

    private val askedQuestions = ConcurrentHashMap.newKeySet<Any>()

    val droppedByQuestion = AtomicLong()

    // ---- question census: decompose the distinct-question population ----

    /** Enabled with -Dopentaint.unfoldClimb.census=true; writes to .census file at shutdown. */
    val censusEnabled: Boolean =
        System.getProperty("opentaint.unfoldClimb.census")?.toBooleanStrictOrNull() ?: false

    /** question -> how many requests carried it. Question = frame | origin | fact | mark. */
    private val census = ConcurrentHashMap<String, java.util.concurrent.atomic.AtomicInteger>()

    fun recordQuestion(frame: String, origin: String, fact: String, mark: String) {
        if (!censusEnabled) return
        census.computeIfAbsent("$frame\u0001$origin\u0001$fact\u0001$mark") {
            java.util.concurrent.atomic.AtomicInteger()
        }.incrementAndGet()
    }

    private fun censusReport(): String = buildString {
        val rows = census.entries.map { it.key.split('\u0001') to it.value.get() }
        val requests = rows.sumOf { it.second }
        appendLine("requests=$requests distinctQuestions=${rows.size}")
        if (rows.isEmpty()) return@buildString

        fun distinct(i: Int) = rows.mapTo(HashSet()) { it.first[i] }.size
        appendLine("distinct: frames=${distinct(0)} origins=${distinct(1)} facts=${distinct(2)} marks=${distinct(3)}")

        // how many requests carry one question
        val mult = rows.groupingBy { it.second }.eachCount().toSortedMap()
        appendLine("requestsPerQuestion histogram (count -> questions):")
        mult.entries.take(15).forEach { (k, v) -> appendLine("  x%-4d %d".format(k, v)) }
        val repeats = rows.sumOf { it.second - 1 }
        appendLine("repeatRequests=$repeats (%.1f%% of all)".format(100.0 * repeats / requests))

        // which component carries the breadth
        fun projDistinct(vararg idx: Int) =
            rows.mapTo(HashSet()) { r -> idx.joinToString("\u0001") { r.first[it] } }.size
        appendLine("projections of the question set:")
        appendLine("  frame                 = ${projDistinct(0)}")
        appendLine("  origin                = ${projDistinct(1)}")
        appendLine("  fact                  = ${projDistinct(2)}")
        appendLine("  mark                  = ${projDistinct(3)}")
        appendLine("  origin x mark         = ${projDistinct(1, 3)}")
        appendLine("  origin x fact         = ${projDistinct(1, 2)}")
        appendLine("  origin x fact x mark  = ${projDistinct(1, 2, 3)}   <- the questions ignoring the asking frame")
        appendLine("  frame x origin        = ${projDistinct(0, 1)}")

        fun top(name: String, idx: IntArray, n: Int) {
            appendLine("top $n by $name (questions, requests):")
            rows.groupBy { r -> idx.joinToString(" | ") { r.first[it] } }
                .map { (k, v) -> Triple(k, v.size, v.sumOf { it.second }) }
                .sortedByDescending { it.second }.take(n)
                .forEach { appendLine("  q=%-7d r=%-7d %s".format(it.second, it.third, it.first.take(180))) }
        }
        top("frame", intArrayOf(0), 15)
        top("origin", intArrayOf(1), 15)
        top("mark", intArrayOf(3), 15)
        top("origin x fact x mark", intArrayOf(1, 2, 3), 10)
    }

    /** Distinct questions actually handled. */
    val questionCount: Int get() = askedQuestions.size

    /** @return true when this question has already been asked at this frame. */
    fun questionAlreadyAsked(key: Any): Boolean {
        if (!questionMemo) return false
        if (askedQuestions.add(key)) return false
        droppedByQuestion.incrementAndGet()
        return true
    }

    val statsEnabled: Boolean =
        System.getProperty("opentaint.unfoldClimb.stats")?.toBooleanStrictOrNull() ?: true

    private val seen = ConcurrentHashMap.newKeySet<Any>()

    // ---- request tracing and suppression, for the minimisation harness ----

    /** Record every request the handler sees, keyed structurally. */
    @Volatile
    var traceEnabled: Boolean = false

    /** Occurrence count per structural request key, in first-seen order. */
    val trace: MutableMap<String, Int> = java.util.Collections.synchronizedMap(LinkedHashMap())

    /**
     * When non-null, only requests whose key is in this set are handled; every other request is a
     * no-op. `null` means handle everything, i.e. the unbounded engine.
     */
    @Volatile
    var allow: Set<String>? = null

    val suppressedCount = AtomicLong()

    fun reset() {
        seen.clear()
        askedQuestions.clear()
        trace.clear()
        allow = null
        traceEnabled = false
        questionMemo = System.getProperty("opentaint.unfoldClimb.questionMemo")?.toBooleanStrictOrNull() ?: false
        listOf(
            reposted, droppedByMemo, droppedByDepth, droppedByRefined,
            answeredLocally, maxDepthSeen, suppressedCount, droppedByQuestion
        ).forEach { it.set(0) }
    }

    /** Structural identity of one request as the handler sees it. */
    fun requestKey(method: Any, fact: Any, mark: Any, effect: String, delta: Any?, suffix: Any?): String =
        ("$method | fact=$fact | mark=$mark | $effect | delta=${render(delta)} | suffix=${render(suffix)}")

    /**
     * Data-class toString on the access-tree deltas leaks the ApManager's identity hash, which is
     * fresh per analysis run. Strip identity hashes so a key means the same thing across runs.
     */
    private fun render(v: Any?): String = v?.toString()
        ?.replace(Regex("@[0-9a-f]{4,}"), "")
        ?.replace(Regex("apManager=[^,]*, "), "")
        ?.replace("\n", " ")
        ?.trim() ?: "-"

    /**
     * Records the request and reports whether the handler should act on it.
     * Returns false when the minimisation harness has suppressed this key.
     */
    fun admit(key: String): Boolean {
        if (traceEnabled) {
            synchronized(trace) { trace[key] = (trace[key] ?: 0) + 1 }
        }
        val allowed = allow
        if (allowed != null && key !in allowed) {
            suppressedCount.incrementAndGet()
            return false
        }
        return true
    }

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
            Runtime.getRuntime().addShutdownHook(Thread {
                System.err.println(report())
                if (censusEnabled) {
                    runCatching {
                        java.io.File(System.getProperty("opentaint.unfoldClimb.censusOut") ?: "unfold-census.txt")
                            .writeText(censusReport())
                    }
                }
            })
        }
    }

    fun report(): String = buildString {
        append("unfoldClimb: disabled=").append(disabled)
        append(" memo=").append(memoEnabled)
        append(" maxDepth=").append(maxDepth)
        append(" suffixInKey=").append(suffixInKey)
        append(" unrefinedOnly=").append(unrefinedOnly)
        append(" questionMemo=").append(questionMemo)
        append(" | answeredLocally=").append(answeredLocally.get())
        append(" reposted=").append(reposted.get())
        append(" droppedByMemo=").append(droppedByMemo.get())
        append(" droppedByDepth=").append(droppedByDepth.get())
        append(" droppedByRefined=").append(droppedByRefined.get())
        append(" droppedByQuestion=").append(droppedByQuestion.get())
        append(" questions=").append(askedQuestions.size)
        append(" distinctKeys=").append(seen.size)
        append(" maxFactDepth=").append(maxDepthSeen.get())
    }
}

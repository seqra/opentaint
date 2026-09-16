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

    /**
     * One handler invocation. `unique` is the tuple that makes this request distinct work --
     * (frame, edge fact, origin, fact, mark, suffix) -- which is what the summary storage keys on
     * (CommonFactSideEffectSummary: base + initialAccess + SideEffectKind, exclusions merged as the
     * value). `question` drops the edge fact and the suffix, leaving what is actually being asked.
     * Identical invocations collapse in storage on their own; the interesting number is how many
     * STORAGE-DISTINCT requests share a question, because those are droppable but not deduplicated.
     */
    fun recordRequest(frame: String, origin: String, fact: String, mark: String, edgeFact: String, suffix: String) {
        if (!censusEnabled) return
        val q = "$frame\u0001$origin\u0001$fact\u0001$mark"
        val u = "$q\u0001$edgeFact\u0001$suffix"
        census.computeIfAbsent(u) { java.util.concurrent.atomic.AtomicInteger() }.incrementAndGet()
    }

    private fun censusReport(): String = buildString {
        // row = [frame, origin, fact, mark, edgeFact, suffix] -> invocations
        val rows = census.entries.map { it.key.split('\u0001') to it.value.get() }
        if (rows.isEmpty()) return@buildString
        val invocations = rows.sumOf { it.second }

        fun key(r: List<String>, vararg i: Int) = i.joinToString("\u0001") { r[it] }
        val questions = rows.mapTo(HashSet()) { key(it.first, 0, 1, 2, 3) }.size
        val unique = rows.size   // storage-distinct: frame x origin x fact x mark x edgeFact x suffix

        appendLine("invocations     = $invocations")
        appendLine("uniqueRequests  = $unique   <- storage-distinct; identical ones already collapse there")
        appendLine("questions       = $questions   <- what is actually being asked")
        appendLine("DROPPABLE UNIQUE = ${unique - questions} of $unique (%.1f%%)"
            .format(100.0 * (unique - questions) / unique))
        appendLine("identical-invocation collapse already done by storage = ${invocations - unique} (%.1f%% of invocations)"
            .format(100.0 * (invocations - unique) / invocations))

        fun distinct(i: Int) = rows.mapTo(HashSet()) { it.first[i] }.size
        appendLine("distinct: frames=${distinct(0)} origins=${distinct(1)} facts=${distinct(2)} marks=${distinct(3)} edgeFacts=${distinct(4)} suffixes=${distinct(5)}")

        val perQuestion = rows.groupBy { key(it.first, 0, 1, 2, 3) }
        appendLine("uniqueRequestsPerQuestion histogram (count -> questions):")
        perQuestion.values.groupingBy { it.size }.eachCount().toSortedMap().entries.take(15)
            .forEach { (k, v) -> appendLine("  x%-4d %d".format(k, v)) }

        // which component fabricates the uniqueness inside a question
        val edgeFactVariants = perQuestion.values.sumOf { g -> g.mapTo(HashSet()) { it.first[4] }.size }
        val suffixVariants = perQuestion.values.sumOf { g -> g.mapTo(HashSet()) { it.first[5] }.size }
        appendLine("attribution across $questions questions:")
        appendLine("  summed distinct edgeFacts = $edgeFactVariants (%.2f per question)".format(1.0 * edgeFactVariants / questions))
        appendLine("  summed distinct suffixes  = $suffixVariants (%.2f per question)".format(1.0 * suffixVariants / questions))
        appendLine("  unique/question           = %.2f".format(1.0 * unique / questions))

        fun projQ(vararg idx: Int) = rows.mapTo(HashSet()) { r -> idx.joinToString("\u0001") { r.first[it] } }.size
        appendLine("projections of the QUESTION set:")
        appendLine("  origin x fact x mark = ${projQ(1, 2, 3)}   <- questions ignoring the asking frame")
        appendLine("  origin x fact        = ${projQ(1, 2)}   <- and ignoring the mark")

        fun top(name: String, idx: IntArray, n: Int) {
            appendLine("top $n by $name (q = questions, u = unique requests):")
            rows.groupBy { r -> idx.joinToString(" | ") { r.first[it] } }
                .map { (k, v) -> Triple(k, v.mapTo(HashSet()) { key(it.first, 0, 1, 2, 3) }.size, v.size) }
                .sortedByDescending { it.third }.take(n)
                .forEach { appendLine("  q=%-7d u=%-7d %s".format(it.second, it.third, it.first.take(170))) }
        }
        top("frame", intArrayOf(0), 12)
        top("mark", intArrayOf(3), 10)
        top("origin x fact x mark", intArrayOf(1, 2, 3), 10)
    }

    // ---- hypothesis: the ApRefinement delta is the edge fact's own tail ----

    /** Per storage key: how often the predicate held / did not hold. */
    val deltaTailTrue: MutableMap<String, Int> = java.util.Collections.synchronizedMap(HashMap())
    val deltaTailFalse: MutableMap<String, Int> = java.util.Collections.synchronizedMap(HashMap())

    fun recordDeltaTail(key: String, isTail: Boolean) {
        if (!traceEnabled) return
        val m = if (isTail) deltaTailTrue else deltaTailFalse
        synchronized(m) { m[key] = (m[key] ?: 0) + 1 }
    }

    /** Drop a request whose ApRefinement delta is exactly the tail of the F2F initial fact. */
    @Volatile
    var dropDeltaTail: Boolean =
        System.getProperty("opentaint.unfoldClimb.dropDeltaTail")?.toBooleanStrictOrNull() ?: false

    val droppedByDeltaTail = AtomicLong()

    /** Why the predicate did or did not decide, over every f2f unfold request. */
    val tailTrue = AtomicLong()
    val tailFalse = AtomicLong()
    val tailNotApRefinement = AtomicLong()
    val tailEmptyDelta = AtomicLong()
    val tailBranching = AtomicLong()

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
        deltaTailTrue.clear()
        deltaTailFalse.clear()
        dropDeltaTail = System.getProperty("opentaint.unfoldClimb.dropDeltaTail")?.toBooleanStrictOrNull() ?: false
        questionMemo = System.getProperty("opentaint.unfoldClimb.questionMemo")?.toBooleanStrictOrNull() ?: false
        listOf(
            reposted, droppedByMemo, droppedByDepth, droppedByRefined,
            answeredLocally, maxDepthSeen, suppressedCount, droppedByQuestion, droppedByDeltaTail,
            tailTrue, tailFalse, tailNotApRefinement, tailEmptyDelta, tailBranching
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
        append(" droppedByDeltaTail=").append(droppedByDeltaTail.get())
        append(" | tail: true=").append(tailTrue.get())
        append(" false=").append(tailFalse.get())
        append(" notApRef=").append(tailNotApRefinement.get())
        append(" emptyDelta=").append(tailEmptyDelta.get())
        append(" branching=").append(tailBranching.get())
        append(" questions=").append(askedQuestions.size)
        append(" distinctKeys=").append(seen.size)
        append(" maxFactDepth=").append(maxDepthSeen.get())
    }
}

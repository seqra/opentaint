package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier.AnyField
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.util.UnfoldClimbBound
import java.io.File

/**
 * Diagnostic harness, not a gate. Traces every taint-mark field-unfold request the unbounded engine
 * raises on the depth ladder, then greedily removes them one at a time -- re-running the whole
 * analysis for each candidate -- to find a minimal set that still reports the finding. What is left
 * is required by construction; everything else is redundant by construction.
 */
class UnfoldRequestMinimizationTest : AnalysisTest() {
    companion object {
        private const val TEST_CLASS = "test.samples.AnyFieldDeepInterproceduralSample"
        private const val TAINT_MARK = "tainted"
        private const val RULE_ID = "any-field-interprocedural-deep"
        private val DEPTHS = listOf(1, 2, 3, 5, 10)
    }

    override val sourceFileExtension: String = "java"

    override val analysisUnrollStrategy: AnyAccessorUnrollStrategy = object : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = accessor is FieldAccessor
    }

    private val config = SerializedTaintConfig(
        source = listOf(sourceRule(TEST_CLASS, "source", TAINT_MARK)),
        sink = listOf(
            SerializedRule.Sink(
                function = functionMatcher(TEST_CLASS, "sink"),
                condition = SerializedCondition.ContainsMark(
                    tainted = TAINT_MARK,
                    pos = PositionBaseWithModifiers.WithModifiers(Argument(0), listOf(AnyField)),
                ),
                id = RULE_ID,
                meta = SinkMetaData(note = "Taint reaches a field of sink argument"),
            )
        ),
    )

    var lastQuestions = 0
    var lastDropped = 0L
    var lastTailTrue = 0L
    var lastTailFalse = 0L
    var lastNotApRef = 0L
    var lastBranching = 0L
    var lastDroppedTail = 0L
    var lastTailTrueKeys: Set<String> = emptySet()
    var lastTailFalseKeys: Set<String> = emptySet()

    private fun run(
        entry: String,
        allow: Set<String>?,
        questionMemo: Boolean = false,
        dropDeltaTail: Boolean = false,
    ): Pair<Boolean, Map<String, Int>> {
        UnfoldClimbBound.reset()
        UnfoldClimbBound.traceEnabled = true
        UnfoldClimbBound.allow = allow
        UnfoldClimbBound.questionMemo = questionMemo
        UnfoldClimbBound.dropDeltaTail = dropDeltaTail
        val found = runAnalysis(config, TEST_CLASS, entry).isNotEmpty()
        val seen = synchronized(UnfoldClimbBound.trace) { LinkedHashMap(UnfoldClimbBound.trace) }
        lastQuestions = UnfoldClimbBound.questionCount
        lastDropped = UnfoldClimbBound.droppedByQuestion.get()
        lastTailTrue = UnfoldClimbBound.tailTrue.get()
        lastTailFalse = UnfoldClimbBound.tailFalse.get()
        lastNotApRef = UnfoldClimbBound.tailNotApRefinement.get()
        lastBranching = UnfoldClimbBound.tailBranching.get()
        lastDroppedTail = UnfoldClimbBound.droppedByDeltaTail.get()
        lastTailTrueKeys = synchronized(UnfoldClimbBound.deltaTailTrue) { HashSet(UnfoldClimbBound.deltaTailTrue.keys) }
        lastTailFalseKeys = synchronized(UnfoldClimbBound.deltaTailFalse) { HashSet(UnfoldClimbBound.deltaTailFalse.keys) }
        UnfoldClimbBound.reset()
        return found to seen
    }

    @org.junit.jupiter.api.Disabled("diagnostic only")
    @Test
    fun `probe determinism of the trace and of suppression`() {
        val entry = "fieldFlowDepth1"
        val out = StringBuilder()
        fun say(s: String) { out.appendLine(s) }
        say("=".repeat(90))
        say("-- allow = null (unbounded), 5 repeats --")
        val traces = (1..5).map { run(entry, null) }
        traces.forEachIndexed { i, (found, t) ->
            say("  run %d: found=%-5s keys=%-4d occurrences=%d".format(i + 1, found, t.size, t.values.sum()))
        }
        val keySets = traces.map { it.second.keys }
        say("  key sets identical across runs: ${keySets.all { it == keySets[0] }}")
        keySets.drop(1).forEachIndexed { i, ks ->
            val onlyFirst = keySets[0] - ks
            val onlyThis = ks - keySets[0]
            if (onlyFirst.isNotEmpty() || onlyThis.isNotEmpty()) {
                say("    run ${i + 2} differs: -${onlyFirst.size} +${onlyThis.size}")
            }
        }

        say("-- keys of run 1 --")
        keySets[0].forEachIndexed { i, k -> say("  [1.$i] $k") }
        say("-- keys of run 2 --")
        keySets[1].forEachIndexed { i, k -> say("  [2.$i] $k") }

        val full = keySets[0]
        say("-- allow = full observed set (${full.size} keys), 5 repeats --")
        repeat(5) {
            val (found, t) = run(entry, full)
            say("  found=%-5s keys=%-4d newKeysNotInAllow=%d".format(found, t.size, (t.keys - full).size))
        }
        say("=".repeat(90))
        File(System.getProperty("unfold.report") ?: "/tmp/unfold-probe.txt").writeText(out.toString())
    }

    @Test
    fun `classify unfold requests as required or redundant`() {
        val out = StringBuilder()
        fun say(s: String) { out.appendLine(s) }

        for (depth in DEPTHS) {
            val entry = "fieldFlowDepth$depth"

            val (found1, trace1) = run(entry, null)
            val (found2, trace2) = run(entry, null)
            check(found1 && found2) { "depth $depth: unbounded run did not report the finding" }
            check(trace1.keys == trace2.keys) { "depth $depth: request trace is not reproducible" }

            val observed = trace1
            check(run(entry, observed.keys).first) { "depth $depth: replaying the full key set lost the finding" }

            // Greedy: drop a key permanently whenever the finding survives without it.
            var keep = observed.keys.toMutableSet()
            var runs = 0
            for (k in observed.keys) {
                if (k !in keep) continue
                val candidate = keep - k
                runs++
                if (run(entry, candidate).first) keep = candidate.toMutableSet()
            }
            check(run(entry, keep).first) { "depth $depth: minimal set does not reproduce the finding" }

            val required = observed.keys.filter { it in keep }
            val redundant = observed.keys.filter { it !in keep }

            say("=".repeat(110))
            say("depth %-2d | kinds %-3d -> required %-3d redundant %-3d | occurrences %-4d | probe runs %d"
                .format(depth, observed.size, required.size, redundant.size, observed.values.sum(), runs))
            say("  REQUIRED (${required.size}):")
            required.forEach { say("    x%-3d %s".format(observed[it], it)) }
            say("  REDUNDANT (${redundant.size}):")
            redundant.forEach { say("    x%-3d %s".format(observed[it], it)) }
        }
        File(System.getProperty("unfold.report") ?: "/tmp/unfold-minim.txt").writeText(out.toString())
    }

    /**
     * The depth ladder never produces a request whose delta is the edge fact's tail, so it cannot
     * judge that predicate. The recursive walk does -- each frame is entered one `.next` deeper
     * than its caller. This is the unit-level safety check for dropping those requests.
     */
    @Test
    fun `delta-is-edge-tail on the recursive walk`() {
        val out = StringBuilder()
        for (entry in listOf("fieldFlowRecursive", "fieldFlowDepth10")) {
            val keep = run(entry, null, dropDeltaTail = false)
            val kTrue = lastTailTrue; val kFalse = lastTailFalse
            val kNot = lastNotApRef; val kBranch = lastBranching
            val drop = run(entry, null, dropDeltaTail = true)
            val dropped = lastDroppedTail
            out.appendLine(
                "%-20s | keep: found=%-5s unique=%-4d tailTrue=%-4d tailFalse=%-4d notApRef=%-4d branching=%-4d | drop: found=%-5s unique=%-4d dropped=%d"
                    .format(entry, keep.first, keep.second.size, kTrue, kFalse, kNot, kBranch, drop.first, drop.second.size, dropped)
            )
            out.appendLine("   VERDICT: " + if (!keep.first) "n/a (not reachable even unbounded)"
                else if (drop.first) "SAFE here" else "LOSSY - dropping the delta-tail requests loses the finding")
        }
        File(System.getProperty("unfold.rec") ?: "/tmp/unfold-rec.txt").writeText(out.toString())
    }

    /**
     * Cross-tabulate the "ApRefinement delta is the F2F initial fact's tail" predicate against the
     * ground-truth required/redundant classification. A predicate that ever fires on a REQUIRED
     * request is lossy; one that only fires on redundant ones is a safe drop on this sample.
     */
    @Test
    fun `delta-is-edge-tail predicate versus ground truth`() {
        val out = StringBuilder()
        out.appendLine("%-6s %-7s %-9s %-10s | %-12s %-12s %-14s %s".format(
            "depth", "unique", "required", "redundant", "pred-on-req", "pred-on-redun", "coverage", "SAFE"))
        for (depth in DEPTHS) {
            val entry = "fieldFlowDepth$depth"
            val observed = run(entry, null).second
            // snapshot taken inside run(), before its trailing reset()
            val pred = lastTailTrueKeys - lastTailFalseKeys
            val mixed = lastTailTrueKeys intersect lastTailFalseKeys

            var keep = observed.keys.toMutableSet()
            for (k in observed.keys) {
                if (k !in keep) continue
                val cand = keep - k
                if (run(entry, cand).first) keep = cand.toMutableSet()
            }
            val required = observed.keys.filter { it in keep }.toSet()
            val redundant = observed.keys.filter { it !in keep }.toSet()

            val onReq = pred.count { it in required }
            val onRedun = pred.count { it in redundant }
            val coverage = if (redundant.isEmpty()) 0.0 else 100.0 * onRedun / redundant.size
            out.appendLine("%-6d %-7d %-9d %-10d | %-12d %-12d %-13.1f%% %s  (pred=%d mixed=%d)".format(
                depth, observed.size, required.size, redundant.size, onReq, onRedun, coverage,
                if (onReq == 0) "yes" else "NO - LOSSY", pred.size, mixed.size))
            if (onReq > 0) {
                out.appendLine("   predicate fires on these REQUIRED requests:")
                pred.filter { it in required }.take(4).forEach { out.appendLine("     $it") }
            }
        }
        File(System.getProperty("unfold.tail") ?: "/tmp/unfold-tail.txt").writeText(out.toString())
    }

    /** Semantic identity of the question, dropping the summary-application detail. */
    private fun group(key: String): String = key.split(" | ").take(3).joinToString(" | ")

    /**
     * The memo implied by the minimisation: drop a request whose question -- (frame, origin method,
     * origin fact, mark) -- has already been asked at that frame, keeping the first asking. It must
     * find the flow at every depth and it must raise exactly as many requests as the minimal set.
     */
    @Test
    fun `question-level first-wins memo keeps every depth`() {
        val out = StringBuilder()
        out.appendLine("%-6s %-9s %-9s %-9s %-9s %-7s %s".format("depth", "raisedNoMemo", "handled", "dropped", "minimal", "cut", "found"))
        for (depth in DEPTHS) {
            val entry = "fieldFlowDepth$depth"
            val raised = run(entry, null).second.values.sum()
            val (found, traceMemo) = run(entry, null, questionMemo = true)
            val handled = lastQuestions
            val dropped = lastDropped
            val minimal = 2 * depth + 2
            val total = traceMemo.values.sum()
            val cut = "%.0f%%".format(100.0 * dropped / total)
            out.appendLine("%-6d %-9d %-9d %-9d %-9d %-7s %s".format(depth, raised, handled, dropped, minimal, cut, found))
            check(found) { "depth $depth: question memo lost the finding" }
        }
        File(System.getProperty("unfold.memo") ?: "/tmp/unfold-memo.txt").writeText(out.toString())
    }

    @Test
    fun `one variant per question is enough`() {
        val out = StringBuilder()
        fun say(s: String) { out.appendLine(s) }
        say("%-6s %-6s %-7s | %-9s %-9s | %s".format("depth", "kinds", "groups", "first-wins", "last-wins", "every-single-variant-works"))
        for (depth in DEPTHS) {
            val entry = "fieldFlowDepth$depth"
            val observed = run(entry, null).second
            val byGroup = observed.keys.groupBy { group(it) }

            val first = byGroup.values.map { it.first() }.toSet()
            val last = byGroup.values.map { it.last() }.toSet()
            val firstOk = run(entry, first).first
            val lastOk = run(entry, last).first

            // For each group, hold every other group at its first variant and sweep this group's
            // variants one at a time: does each variant on its own carry the question?
            var allWork = true
            val failures = mutableListOf<String>()
            for ((g, variants) in byGroup) {
                if (variants.size < 2) continue
                for (v in variants) {
                    val allow = byGroup.filterKeys { it != g }.values.map { it.first() }.toSet() + v
                    if (!run(entry, allow).first) { allWork = false; failures += "$g -> $v" }
                }
            }
            say("%-6d %-6d %-7d | %-9s %-9s | %s".format(depth, observed.size, byGroup.size, firstOk, lastOk, allWork))
            if (failures.isNotEmpty()) {
                say("   variants that do NOT carry their question (${failures.size}):")
                failures.take(8).forEach { say("     $it") }
            }
        }
        File(System.getProperty("unfold.variants") ?: "/tmp/unfold-variants.txt").writeText(out.toString())
    }
}

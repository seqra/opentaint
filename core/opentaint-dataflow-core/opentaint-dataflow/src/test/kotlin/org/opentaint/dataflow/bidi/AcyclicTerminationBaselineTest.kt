package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.EndReason
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.TERMINATION_BASELINE_LAST_RUN
import org.opentaint.dataflow.bidi.fixtures.TerminationBaselinePolicy
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Duration.Companion.seconds

class AcyclicTerminationBaselineTest {
    private data class Case(
        val name: String,
        val producer: List<String>,
        val read: List<String>,
        val write: List<String>,
        val calls: Int,
        val wrapper: Boolean = false,
        val overwriteInput: List<String> = emptyList(),
        val overwriteOutput: List<String> = emptyList(),
        val protect: Boolean = false,
    )

    // choose(x) returns either x.<read> or a new object holding x at <write>.
    private fun run(case: Case) = DriverFixtures().use { f ->
        val p = f.program
        val x = AccessPathBase.Argument(0)
        val result = AccessPathBase.Return
        val temporary = AccessPathBase.LocalVar(0)
        val locals = List(case.calls + 1) { AccessPathBase.LocalVar(it) }
        val mark = MarkSlot.Concrete(p.mark("T"))
        fun path(fields: List<String>) = fields.map(p::field)
        fun straight(name: String, exit: Int) =
            p.method(name, List(exit + 1) { if (it == exit) emptyList() else listOf(it + 1) }, exit).key()
        fun call(owner: MethodKey, index: Int, from: AccessPathBase, to: AccessPathBase, callee: MethodKey) {
            p.call(owner, index, CallPlan(setOf(from, to), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(
                    ZERO_KEEP, starEdge(from, emptyList(), x, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(
                    ZERO_KEEP, starEdge(result, emptyList(), to, emptyList()))),
            ), emptyList(), BEFORE, AFTER))
        }
        fun clear(base: AccessPathBase, fields: List<String>) = MicroEdgeBuilder().apply {
            write(base, path(fields), weak = false, values = emptyList(), aliasPaths = emptyList())
        }.build()

        val root = straight("entry", case.calls + 1)
        val choose = p.method("choose", listOf(listOf(1), listOf(2, 3), listOf(4), listOf(4),
            listOf(5), listOf(6), emptyList()), 6).key()
        if (case.overwriteInput.isNotEmpty()) p.statement(choose, 1, clear(x, case.overwriteInput))
        check(!case.protect || case.overwriteInput.isEmpty())
        if (case.protect) {
            val keep = f.summary(ZERO_KEEP, keepEdge(x))
            p.call(choose, 1, CallPlan(setOf(x), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, listOf(CleanStep.Clean(Cleaner(x, null, CleanReach.EXACT, mark.mark)))),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), emptyList(), BEFORE, AFTER))
        }
        p.statement(choose, 2, MicroEdgeBuilder().apply { read(temporary, x, path(case.read)) }.build())
        p.statement(choose, 3, MicroEdgeBuilder().apply {
            write(temporary, path(case.write), weak = false, values = listOf(x), aliasPaths = emptyList())
        }.build())
        if (case.overwriteOutput.isNotEmpty()) p.statement(choose, 4, clear(temporary, case.overwriteOutput))
        p.statement(choose, 5, MicroEdgeBuilder().apply { move(result, temporary) }.build())

        val callee = if (case.wrapper) straight("wrapper", 2).also { call(it, 1, x, result, choose) } else choose
        p.entry(root, RuleStatement(f.summary(ZERO_KEEP, PathEdge(ZERO_FACT,
            PathFact(locals.first(), path(case.producer), Tail.ANY_TAINT, mark), ExclusionSet.Empty)),
            StatementSummary.EMPTY, emptyList()))
        repeat(case.calls) { call(root, it + 1, locals[it], locals[it + 1], callee) }
        val observer = SinkRule(f.rule("observe"), 0,
            listOf(p.pattern(locals.last(), tail = Tail.ANY, mark = mark)), emptyList())
        p.exit(root, case.calls + 1, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(observer)), false, emptySet()))
        val driver = f.driver(TerminationBaselinePolicy, 60.seconds, run1MarkMode = MarkMode.FULL)
        val report = driver.analyze(listOf(root))
        val saved = driver.frontiers.last()
        println("TERMINATION_BASELINE ${case.name} run=${report.end.run} reason=${report.end.reason} " +
            "pairs=${saved.demandEdges.values.sum()} targets=${saved.targetDemand} " +
            "confirmed=${report.entries.count { !it.provisional }} provisional=${report.entries.count { it.provisional }}")
        assertEquals(RunStatus.COMPLETE, report.end.status)
        assertEquals(EndReason.RUN_LIMIT, report.end.reason)
        assertEquals(TERMINATION_BASELINE_LAST_RUN, report.end.run)
        assertEquals(report.end.run, saved.run)
        assertEquals(1, saved.targetDemand)
        assertEquals(1, report.entries.size)
        assertEquals(case.protect || case.overwriteInput.size == 2, report.entries.single().provisional)
    }

    @Test fun rootMayRenewal() = run(Case("root MAY", listOf("f"), listOf("f", "g"), listOf("f"), 2))
    @Test fun globalCutGrowth() = run(Case("global cut", emptyList(), listOf("f", "f"), listOf("f", "f"), 2))
    @Test fun protectedGlobalCutGrowth() = run(Case("protected global cut", emptyList(), listOf("f", "f"),
        listOf("f", "f"), 2, protect = true))
    @Test fun nestedSavedReplay() = run(Case("nested saved replay", listOf("f", "g"), listOf("f", "f"),
        listOf("f", "f"), 3, wrapper = true))
    @Test fun overwriteSavedReplay() = run(Case("overwrite saved replay", listOf("f", "g"), listOf("f", "f"),
        listOf("f", "f"), 3, wrapper = true, overwriteInput = listOf("g"), overwriteOutput = listOf("g")))
    @Test fun exactOriginNestedWrite() = run(Case("exact-origin nested write", listOf("g"), listOf("f"),
        listOf("f"), 1, overwriteInput = listOf("f", "g"), overwriteOutput = listOf("f", "g")))
}

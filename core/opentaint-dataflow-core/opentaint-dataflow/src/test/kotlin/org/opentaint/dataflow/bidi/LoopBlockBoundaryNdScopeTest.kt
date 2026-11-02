package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** The selected shared normal loop exit keeps the accepted branch-union FP. */
class LoopBlockBoundaryNdScopeTest {
    private fun run(separateIngress: Boolean) {
        DriverFixtures().use { f ->
            val p = f.program
            // while (again()) {
            //   if (left()) { p = sourceT(); break; }
            //   if (right()) { q = sourceU(); break; }
            // }
            // Exit rule: CM(p,T) AND CM(q,U).
            // The shared normal loop exit can combine mutually exclusive
            // leave paths. The user explicitly accepts this approximation.
            // The positive control executes both source operations in one AL.
            val branches = if (separateIngress) listOf(
                listOf(1), listOf(2, 4, 7), listOf(3), listOf(6),
                listOf(5), listOf(6), emptyList(), listOf(1), emptyList())
            else listOf(listOf(1), listOf(2, 7), listOf(3), listOf(4),
                listOf(5), listOf(6), emptyList(), listOf(1), emptyList())
            val method = p.method("physical exit ND split=$separateIngress", branches,
                normalExit = 6, exceptionalExit = 8, backwardExitDiscovery = true).key()
            val left = AccessPathBase.LocalVar(0)
            val right = AccessPathBase.LocalVar(1)
            val t = MarkSlot.Concrete(p.mark("T"))
            val u = MarkSlot.Concrete(p.mark("U"))
            p.statement(method, 2, f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT, PathFact(left, emptyList(), Tail.EXACT, t), ExclusionSet.Empty)))
            p.statement(method, 4, f.summary(ZERO_KEEP,
                PathEdge(ZERO_FACT, PathFact(right, emptyList(), Tail.EXACT, u), ExclusionSet.Empty)))
            val sink = SinkRule(f.rule("shared physical exit ND sink"), 0,
                listOf(p.pattern(left, mark = t), p.pattern(right, mark = u)), emptyList())
            p.exit(method, 6, ExitRules(RuleStatement(StatementSummary.EMPTY,
                StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val driver = f.driver(FixedLimits(listOf(1, 1, 2)), 15.seconds, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(method))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId },
                "The shared normal loop exit retains the accepted branch-union witness")
            if (separateIngress) {
                val layout = f.shared.contexts.blockLayout(method)
                val normalExitOwner = layout.ownerOf(6)
                val normalEntries = layout.normalExits.map { it.id }.toSet()
                val first = f.results.first().analyzers.single()
                val local = first.blockOutgoingTargets().filter {
                    it.scope.block == normalExitOwner && it.scope.entry in normalEntries
                }.flatMap { it.rows.asSequence() }.filter { it.target == Target.DemandTarget }.toList()
                for (position in listOf(left, right)) assertTrue(local.any { row ->
                    row.premise.members.any { it.base == position }
                }, "The shared exit must form the full cube and retain each run-1 formal-origin demand arm")
                assertTrue(first.outgoingTargets.any { it.premise.isZero && it.target == Target.DemandTarget })
                assertTrue(f.results.any { result -> result.analyzers.single().targets.any {
                    it.premise.isZero && it.target is Target.NormalTarget
                } }, "Refinement must preserve the accepted false positive as a NORMAL entry finding")
            } else assertTrue(f.results.first().analyzers.single().targets.any {
                it.premise.isZero && it.target is Target.NormalTarget
            }, "A complete ZERO-origin cube in one region is already NORMAL in run-1")
        }
    }

    @Test fun `shared normal loop exit retains the accepted cross branch ND witness`() = run(true)
    @Test fun `exit ND still requires and accepts both marks within the same block entry`() = run(false)
}

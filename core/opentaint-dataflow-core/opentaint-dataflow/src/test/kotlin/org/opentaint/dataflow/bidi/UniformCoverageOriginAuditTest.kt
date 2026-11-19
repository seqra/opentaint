package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.ir.api.common.cfg.CommonInst
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class UniformCoverageOriginAuditTest {
    /** Native scheduler, cuts, source seeds and handoff. Only the test adapter
     * at the final observer models the omission before the common consumer. */
    private fun run(omitByValue: Boolean) {
        DriverFixtures().use { f ->
            val p = f.program
            val graph = listOf(listOf(1, 2), listOf(6), listOf(3), listOf(4),
                listOf(5), listOf(6), listOf(7), emptyList())
            val root = p.method("uniform coverage origin audit", graph, 7).key()
            val x = AccessPathBase.LocalVar(0)
            val a = AccessPathBase.LocalVar(1)
            val b = AccessPathBase.LocalVar(2)
            val merged = AccessPathBase.LocalVar(3)
            val r = AccessPathBase.LocalVar(4)
            val field = p.field("f")
            val mark = MarkSlot.Concrete(p.mark("T"))
            val first = PathEdge(ZERO_FACT, PathFact(merged, emptyList(), Tail.ANY_TAINT, mark), ExclusionSet.Empty)
            val second = PathEdge(ZERO_FACT, PathFact(x, List(4) { field }, Tail.EXACT, mark), ExclusionSet.Empty)
            p.statement(root, 1, f.summary(ZERO_KEEP, first))
            p.statement(root, 2, f.summary(ZERO_KEEP, second))
            fun transfer(from: AccessPathBase, to: AccessPathBase, path: List<Int>) = StatementSummary(
                setOf(AccessPathBase.Zero, from, to),
                listOf(MicroEdge.of(ZERO_KEEP), MicroEdge.of(keepEdge(from)),
                    MicroEdge.of(starEdge(from, path, to, emptyList()))), emptyList(), emptyMap())
            p.statement(root, 3, transfer(x, a, listOf(field)))
            p.statement(root, 4, transfer(a, b, listOf(field)))
            p.statement(root, 5, transfer(b, merged, listOf(field)))
            p.statement(root, 6, transfer(merged, r, emptyList()))
            val observer = SinkRule(f.rule("shared observer"), 0,
                listOf(p.pattern(r, tail = Tail.ANY, mark = mark)), emptyList())
            val end = p.inst(root, 7)
            p.exit(root, 7, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
                listOf(observer)), false, emptySet()))
            val exactTrack = p.pattern(r, listOf(field), Tail.EXACT, mark)
            val normalRuns = linkedSetOf<Int>()
            val deepRuns = linkedSetOf<Int>()
            var eligible = 0
            var omitted = 0
            val driver = f.driver(IncreasingLimits, 20.seconds, invokeRun = { config, owner, timeout ->
                val factory = RunMethodHandlers(MethodLocalServicesFactory { core ->
                    val native = RunMethodLocalServices(core)
                    object : MethodLocalServices by native {
                        override fun checkSinksAt(premise: PremiseKey, node: CommonInst, facts: Facts,
                                                  sinks: List<SinkRule>, at: OperationInput): Triggers {
                            if (config.direction != Direction.FORWARD || core.key != root || node != end || !premise.isZero)
                                return native.checkSinksAt(premise, node, facts, sinks, at)
                            val leaves = f.ops.leaves(facts).toList()
                            if (facts.layer == Layer.NORMAL && exactTrack in leaves) deepRuns += config.index
                            val coarse = facts.layer == Layer.DEMAND && leaves.singleOrNull()?.let {
                                it.fact.base == r && it.fact.path.isEmpty() && it.fact.tail == Tail.ANY &&
                                    it.fact.mark == mark && it.exclusion == ExclusionSet.Empty &&
                                    (facts as? TaintTree)?.nonSubsumable == null
                            } == true
                            if (config.index >= 3 && coarse && config.index in normalRuns) {
                                eligible++
                                if (omitByValue) {
                                    omitted++
                                    return Triggers.NONE
                                }
                            }
                            val result = native.checkSinksAt(premise, node, facts, sinks, at)
                            if (facts.layer == Layer.NORMAL && leaves.singleOrNull()?.let {
                                    it.fact.base == r && it.fact.path.isEmpty() && it.fact.tail == Tail.ANY_TAINT &&
                                        it.fact.mark == mark && it.exclusion == ExclusionSet.Empty &&
                                        (facts as? TaintTree)?.nonSubsumable == null
                                } == true && result.fired.any { it.second == Layer.NORMAL }) normalRuns += config.index
                            return result
                        }
                    }
                }, MethodCallServicesFactory(::RunMethodCallServices))
                f.configs += config
                RunManager(config, owner, factory, quantum = 1).run(timeout).also(f.results::add)
            }, run1MarkMode = MarkMode.FULL)
            val report = driver.analyze(listOf(root))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            assertEquals(EndReason.NO_DEMAND_EDGE, report.end.reason)
            assertEquals(if (omitByValue) 3 else 5, report.end.run)
            assertEquals(1, report.entries.count { !it.provisional })
            assertTrue(eligible > 0)
            assertEquals(omitByValue, omitted > 0)
            assertEquals(if (omitByValue) emptySet<Int>() else setOf(5), deepRuns)
            if (!omitByValue) assertTrue(f.configs.single { it.index == 5 }.seeds
                .allowsSource(root, p.inst(root, 2), second))
        }
    }

    @Test fun `native baseline retains a later exact track from the second source`() = run(omitByValue = false)
    @Test fun `coverage by the uniform value alone loses the second track`() = run(omitByValue = true)
}

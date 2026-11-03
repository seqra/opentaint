package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import java.util.concurrent.CopyOnWriteArrayList
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class JoinedStatePreparationTest {
    @Test fun `real static completion sees released execution and the exact captured exports`() {
        DriverFixtures().use { f ->
            val p = f.program
            val root = p.method("joined lifecycle", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), p.field("f"))
            val mark = MarkSlot.Concrete(p.mark("T"))
            val static = p.pattern(STATIC, path, Tail.EXACT, mark)
            val ret = p.pattern(AccessPathBase.Return, tail = Tail.EXACT, mark = mark)
            val write = PathEdge(ZERO_FACT, static.fact, ExclusionSet.Empty)
            val operation = StaticOperation.Write(OperationId(FormKey(FormOwner(), root.method, root, p.inst(root, 0))), static, write)
            p.entry(root, RuleStatement(f.summary(ZERO_KEEP, write, PathEdge(ZERO_FACT, ret.fact, ExclusionSet.Empty))
                .withStaticOperations(listOf(operation)), StatementSummary.EMPTY, emptyList()))
            val sink = SinkRule(f.rule("joined target"), 0, listOf(ret), emptyList())
            p.exit(root, 2, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            val actors = CopyOnWriteArrayList<RunMethodAnalyzer>()
            val handlers = RunMethodHandlers(MethodLocalServicesFactory(::RunMethodLocalServices),
                MethodCallServicesFactory(::RunMethodCallServices))
            val factory = RunnerHandlerFactory<RunMethodAnalyzer> { port ->
                val actual = handlers.create(port)
                object : RunnerHandler<RunMethodAnalyzer> by actual {
                    override fun createActor(key: MethodKey): RunMethodAnalyzer = actual.createActor(key).also(actors::add)
                }
            }
            val phases = ArrayList<JoinedPreparationPhase>()
            val run = RunManager(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(root)), f.shared, factory, quantum = 1)
            var native: org.opentaint.dataflow.bidi.store.RunSummaryStore? = null
            var targets: Set<TargetSummary>? = null
            run.joinedPreparationObserver = { phase ->
                phases += phase
                if (phase == JoinedPreparationPhase.CAPTURED) {
                    val actor = actors.single()
                    native = actor.summaries
                    targets = actor.targets.toSet()
                    assertTrue(checkNotNull(targets).isNotEmpty(), "Real exit sink produces a Target export")
                }
                if (phase == JoinedPreparationPhase.BEFORE_BIND) {
                    val actor = actors.single()
                    assertTrue(actor.executionReleased)
                    assertFailsWith<IllegalStateException> { actor.edges }
                    assertFailsWith<IllegalStateException> { actor.context }
                    assertSame(native, actor.summaries)
                    assertEquals(targets, actor.targets)
                    assertTrue(actor.summaries.all().any())
                }
            }
            val result = run.run(5.seconds)
            assertEquals(RunStatus.COMPLETE, result.status)
            assertEquals(listOf(JoinedPreparationPhase.CAPTURED, JoinedPreparationPhase.SEALED,
                JoinedPreparationPhase.RELEASED, JoinedPreparationPhase.BEFORE_BIND,
                JoinedPreparationPhase.BOUND, JoinedPreparationPhase.CLOSED), phases,
                "Capture, release and binding must follow the real joined pipeline")
            assertSame(native, result.analyzers.single().summaries)
            assertEquals(targets, result.analyzers.single().targets)
            assertNotNull(result.staticCompletion)
        }
    }
    @Test fun `joined phase failures close once and export no partial result`() {
        for (failedAt in JoinedPreparationPhase.entries) DriverFixtures().use { f ->
            val root = f.program.method("joined failure $failedAt", listOf(listOf(1), emptyList()), 1).key()
            val actors = CopyOnWriteArrayList<RunMethodAnalyzer>()
            val handlers = RunMethodHandlers(MethodLocalServicesFactory(::RunMethodLocalServices),
                MethodCallServicesFactory(::RunMethodCallServices))
            val factory = RunnerHandlerFactory<RunMethodAnalyzer> { port ->
                val actual = handlers.create(port)
                object : RunnerHandler<RunMethodAnalyzer> by actual {
                    override fun createActor(key: MethodKey) = actual.createActor(key).also(actors::add)
                }
            }
            val run = RunManager(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(root)), f.shared, factory, quantum = 1)
            val phases = ArrayList<JoinedPreparationPhase>()
            run.joinedPreparationObserver = { phase ->
                phases += phase
                if (phase == failedAt) error("injected $failedAt")
            }
            val result = run.run(5.seconds)
            assertEquals(RunStatus.FAILED, result.status, "$failedAt")
            assertTrue(result.analyzers.isEmpty(), "$failedAt cannot export actors")
            assertNull(result.staticCompletion, "$failedAt cannot export partial static guidance")
            assertTrue(actors.all { it.executionReleased }, "$failedAt releases every captured method")
            assertEquals(1, phases.count { it == JoinedPreparationPhase.CLOSED }, "$failedAt closes once")
            assertTrue(phases.groupingBy { it }.eachCount().values.all { it == 1 })
            assertEquals(0L, f.shared.normalRuleContributors.retainedRows,
                "RunManager never publishes contributors before the driver's successful barrier")
        }
    }

    @Test fun `later joined cleanup failure is suppressed on the first preparation failure`() {
        DriverFixtures().use { f ->
            val root = f.program.method("joined double failure", listOf(listOf(1), emptyList()), 1).key()
            val run = f.manager(RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(root)))
            val first = IllegalStateException("capture failed")
            val second = IllegalArgumentException("cleanup failed")
            run.joinedPreparationObserver = { phase ->
                if (phase == JoinedPreparationPhase.CAPTURED) throw first
                if (phase == JoinedPreparationPhase.CLOSED) throw second
            }
            val result = run.run(5.seconds)
            assertEquals(RunStatus.FAILED, result.status)
            assertTrue(result.analyzers.isEmpty())
            assertNull(result.staticCompletion)
            assertContentEquals(arrayOf<Throwable>(second), first.suppressed,
                "Cleanup cannot replace the original capture failure")
        }
    }

}

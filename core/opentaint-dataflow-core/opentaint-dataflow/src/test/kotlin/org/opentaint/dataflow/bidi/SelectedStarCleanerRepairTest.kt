package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.RunStatus
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Selected P31/P36 repair. The scalar/table assertions specify the new branch;
 * the driver test obtains every summary from source, cleaner and return code. */
class SelectedStarCleanerRepairTest {
    @Test fun `selected partial STAR has one MAY demand survivor with Empty E in scalar and tree kernels`() {
        StoreFixtures().let { f ->
            val m = f.manager
            val x = AccessPathBase.Argument(0)
            val field = f.field("f")
            val hole = f.field("hole")
            val t = f.mark("T")
            val mark = MarkSlot.Concrete(t)
            val original = m.initial(f.pattern(x, tail = Tail.STAR, mark = mark))
            val input = f.fact(x, tail = Tail.STAR, mark = mark, exclusion = ExclusionSet.of(hole))
            val expected = Pattern(PathFact(x, emptyList(), Tail.ANY, mark), ExclusionSet.Empty)
            for (mode in listOf(ApMode(true, Direction.FORWARD, 3, MarkMode.FULL),
                ApMode(false, Direction.FORWARD, 3), ApMode(false, Direction.BACKWARD, 3))) {
                for (at in listOf(emptyList(), listOf(field))) {
                    val cleaner = Cleaner(x, m.path(at), CleanReach.EXACT, t)
                    val scalar = cleanRes(cleaner, Conclusion(f.ops.leaves(input).single().fact,
                        f.ops.leaves(input).single().exclusion, false), mode.run1).facts.single()
                    assertEquals(expected, Pattern(scalar.fact, scalar.exclusion))
                    assertTrue(scalar.demand)
                    val out = CollectingOut()
                    f.ops.clean(input, original, cleaner, mode, out)
                    assertEquals(listOf(expected), out.results.flatMap { f.ops.leaves(it).toList() })
                    assertEquals(Layer.DEMAND, out.results.single().layer)
                    assertNotNull((out.results.single() as TaintTree).nonSubsumable)
                }
            }
        }
    }

    @Test fun `disjoint excluded and below-root cleaner controls do not widen to MAY`() {
        StoreFixtures().let { f ->
            val m = f.manager
            val x = AccessPathBase.Argument(0)
            val field = f.field("f")
            val t = f.mark("T")
            val u = f.mark("U")
            val mark = MarkSlot.Concrete(t)
            val original = m.initial(f.pattern(x, tail = Tail.STAR, mark = mark))
            val mode = ApMode(false, Direction.FORWARD, 3)
            fun clean(input: Facts, cl: Cleaner): List<Facts> = CollectingOut().also {
                f.ops.clean(input, original, cl, mode, it)
            }.results
            val star = f.fact(x, tail = Tail.STAR, mark = mark)
            val excluded = f.fact(x, tail = Tail.STAR, mark = mark, exclusion = ExclusionSet.of(field))
            val disjoint = clean(excluded, Cleaner(x, m.path(listOf(field)), CleanReach.EXACT, t))
            assertEquals(listOf(f.ops.leaves(excluded).single()), disjoint.flatMap { f.ops.leaves(it).toList() })
            assertEquals(Layer.NORMAL, disjoint.single().layer)
            assertNotNull((disjoint.single() as TaintTree).nonSubsumable,
                "The existing selected-survivor protection producer remains unchanged")
            val other = clean(star, Cleaner(x, null, CleanReach.EXACT, u))
            assertEquals(listOf(star), other)
            val below = clean(star, Cleaner(x, null, CleanReach.BELOW, t))
            assertEquals(Tail.EXACT, f.ops.leaves(below.single()).single().fact.tail)
            assertTrue(clean(star, Cleaner(x, null, CleanReach.AT_AND_BELOW, null)).isEmpty(),
                "RemoveAll still kills the entire position")
            val exact = f.fact(x, listOf(field), Tail.EXACT, mark)
            val exactKept = clean(exact, Cleaner(x, null, CleanReach.EXACT, t))
            assertEquals(listOf(f.ops.leaves(exact).single()), exactKept.flatMap { f.ops.leaves(it).toList() })
            assertEquals(Layer.NORMAL, exactKept.single().layer)
        }
    }

    @Test fun `bulk FULL selected STAR cleanup equals scalar output and keeps unrelated marks`() {
        StoreFixtures().let { f ->
            val m = f.manager
            val x = AccessPathBase.Argument(0)
            val t = f.mark("T")
            val u = f.mark("U")
            val mark = MarkSlot.Concrete(t)
            val input = f.fact(x, tail = Tail.STAR, mark = mark, layer = Layer.DEMAND)
            val original = m.initial(f.pattern(x, tail = Tail.STAR, mark = mark))
            val cleaner = Cleaner(x, null, CleanReach.EXACT, t)
            val mode = ApMode(true, Direction.FORWARD, 1, MarkMode.FULL)
            val scalar = CollectingOut().also { f.ops.clean(input, original, cleaner, mode, it) }
            val bulk = CollectingOut().also {
                f.ops.cleanSelectedFullMask(input, original, cleaner, m.markSetOf(t) + u, mode,
                    { fail("A concrete input does not produce mark requests") }, it)
            }
            fun decoded(out: CollectingOut) = out.results.flatMap { value ->
                f.ops.leaves(value).map { Triple(it, value.layer,
                    value is TaintTree && value.nonSubsumable != null) }.toList()
            }.toSet()
            assertEquals(decoded(scalar), decoded(bulk))
            assertEquals(Tail.ANY, f.ops.leaves(bulk.results.single()).single().fact.tail)
        }
    }

    private fun rootCleanerProgram(removeAll: Boolean) {
        DriverFixtures().use { f ->
            val p = f.program
            // main: x.g=sourceT(); r=m(x); sinkT(r.g).
            // m(p): cleanRootT(p); return p.
            val main = p.method("E31 main all=$removeAll", listOf(listOf(1), listOf(2), listOf(3), emptyList()), 3).key()
            val method = p.method("E31 m all=$removeAll", listOf(listOf(1), listOf(2), listOf(3), emptyList()), 3).key()
            val x = AccessPathBase.LocalVar(0)
            val r = AccessPathBase.LocalVar(1)
            val arg = AccessPathBase.Argument(0)
            val ret = AccessPathBase.Return
            val field = p.field("g")
            val t = p.mark("T")
            val mark = MarkSlot.Concrete(t)
            val source = PathEdge(ZERO_FACT, PathFact(x, listOf(field), Tail.EXACT, mark), ExclusionSet.Empty)
            p.entry(main, RuleStatement(f.summary(ZERO_KEEP, source), StatementSummary.EMPTY, emptyList()))
            p.call(main, 1, CallPlan(setOf(x, r), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP,
                    starEdge(x, emptyList(), arg, emptyList()))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(method)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP,
                    starEdge(ret, emptyList(), r, emptyList()))),
            ), emptyList(), BEFORE, AFTER))
            val identity = f.summary(ZERO_KEEP, keepEdge(arg))
            p.call(method, 1, CallPlan(setOf(arg), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, identity),
                CallStage.Actions(BOUND, ADDED, listOf(CleanStep.Clean(Cleaner(arg, null,
                    if (removeAll) CleanReach.AT_AND_BELOW else CleanReach.EXACT, if (removeAll) null else t)))),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, identity),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, identity),
            ), emptyList(), BEFORE, AFTER))
            p.statement(method, 2, MicroEdgeBuilder().apply { move(ret, arg) }.build())
            val sink = SinkRule(f.rule("E31 sink all=$removeAll"), 0,
                listOf(p.pattern(r, listOf(field), mark = mark)), emptyList())
            val keep = f.summary(ZERO_KEEP, keepEdge(r))
            p.call(main, 2, CallPlan(setOf(r), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, keep),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Edges(ADDED, RETURNED, UNRESOLVED, keep),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, keep),
            ), listOf(sink), BEFORE, AFTER))
            val report = f.driver(FixedLimits(listOf(1, 1, 2, 3, 4)), 15.seconds,
                run1MarkMode = MarkMode.FULL).analyze(listOf(main))
            assertEquals(RunStatus.COMPLETE, report.end.status)
            if (removeAll) {
                assertTrue(report.entries.isEmpty(), "RemoveAll must not acquire the selected-mark survivor")
                return
            }
            assertEquals(listOf(sink.rule.id), report.entries.map { it.descriptor.key.ruleId })
            assertEquals(3, report.end.run, "E31 must recover a NORMAL finding by run-3")
            val first = f.results.single { it.runIndex == 1 }.analyzers.single { it.key == method }
            assertTrue(first.summaries.all().any { (_, value) ->
                value.layer == Layer.DEMAND && value is TaintTree && value.nonSubsumable != null &&
                    f.ops.leaves(value).any { it.fact.base == ret && it.fact.tail == Tail.ANY && it.fact.mark == mark }
            }, "The selected STAR survivor must supply the actual MAY/DEMAND handoff")
            val third = f.results.single { it.runIndex == 3 }.analyzers.single { it.key == main }
            assertTrue(third.targets.any { it.premise.isZero && it.target is Target.NormalTarget })
        }
    }

    @Test fun `E31 selected exact-root cleaning preserves the precise child through run three`() = rootCleanerProgram(false)
    @Test fun `E31 RemoveAll negative control cannot report the cleaned child`() = rootCleanerProgram(true)
}

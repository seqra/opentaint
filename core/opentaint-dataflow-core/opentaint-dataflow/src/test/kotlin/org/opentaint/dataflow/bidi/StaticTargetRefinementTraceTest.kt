package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.FixedLimits
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.DriverFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import org.opentaint.dataflow.bidi.store.DemandStore
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/** Small selected-protocol trace. No predefined summaries or report witness adapter. */
class StaticTargetRefinementTraceTest {
    @Test fun `lazy static composition retains paired ZERO Target guidance and the final finding`() {
        DriverFixtures().use { f ->
            val p = f.program
            val main = p.method("root", listOf(listOf(1), listOf(2), emptyList()), 2).key()
            val setter = p.method("set", listOf(listOf(1), emptyList()), 1).key()
            val consumer = p.method("consume", listOf(listOf(1), emptyList()), 1).key()
            val path = listOf(p.ap.accessors.index(ClassStaticAccessor("C")), p.field("f"))
            val mark = MarkSlot.Concrete(p.mark("T"))
            val written = p.pattern(STATIC, path, mark = mark)
            val source = PathEdge(ZERO_FACT, written.fact, ExclusionSet.Empty)
            val writeId = OperationId(FormKey(FormOwner(), setter.method, setter, p.inst(setter, 0)))
            p.statement(setter, 0, f.summary(ZERO_KEEP, source).withStaticOperations(listOf(
                StaticOperation.Write(writeId, written, source))))
            val sink = SinkRule(f.rule("static sink"), 0, listOf(written), emptyList())
            val readId = OperationId(FormKey(FormOwner(), consumer.method, consumer, p.inst(consumer, 1)))
            val checks = StatementSummary.EMPTY.withStaticOperations(listOf(StaticOperation.MarkInput(readId, written)))
            p.exit(consumer, 1, ExitRules(RuleStatement(checks, StatementSummary.EMPTY, listOf(sink)), false, emptySet()))
            fun call(callee: MethodKey) = CallPlan(setOf(AccessPathBase.Zero, STATIC), listOf(
                CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, keepEdge(STATIC))),
                CallStage.Actions(BOUND, ADDED, emptyList()),
                CallStage.Callees(ADDED, RETURNED, listOf(callee)),
                CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, keepEdge(STATIC))),
            ), emptyList(), BEFORE, AFTER)
            p.call(main, 0, call(setter))
            p.call(main, 1, call(consumer))
            val report = f.driver(FixedLimits(listOf(1, 1, 2)), 10.seconds, run1MarkMode = MarkMode.FULL).analyze(listOf(main))
            val controlsField = DemandStore::class.java.getDeclaredField("controls").apply { isAccessible = true }
            val trace = buildString {
                for (config in f.configs) {
                    appendLine("RUN ${config.index} ${config.direction} limit=${config.fieldLimit}")
                    if (config.demand != null) {
                        appendLine("CONTROL ${controlsField.get(config.demand)}")
                        for (key in listOf(main, setter, consumer)) {
                            appendLine("DEMAND ${key.method.name}: ${config.demand.explicitRows(key)}")
                            appendLine("ZERO-ADMISSION ${key.method.name}: ${emitRestrictedInitials(config, f.ops, key, Reach.NORMAL).map { it.initial.toPattern() to it.layer }}")
                        }
                    }
                    val result = f.results.single { it.runIndex == config.index }
                    for (actor in result.analyzers) {
                        fun rows(values: Set<TargetSummary>) = values.map { it.premise.members.map { p -> p.toPattern() } to it.target }
                        appendLine("TARGET ${actor.key.method.name}: raw=${rows(actor.targets)} selected=${rows(actor.outgoingTargets)}")
                        appendLine("SOURCE ${actor.key.method.name}: ${actor.sourceHits?.occurrences()?.toList()}")
                        appendLine("SUMMARY ${actor.key.method.name}: ${actor.summaries.all().map { it.first.members.map { p -> p.toPattern() } to f.ops.leaves(it.second).toList() }.toList()}")
                    }
                }
                appendLine("REPORT ${report.end}: ${report.entries}")
            }
            println(trace)
            val backward = f.configs.single { it.index == 2 }
            assertTrue(backward.demand!!.hasStaticCompletion, trace)
            assertTrue(backward.demand.acceptsTarget(main, f.manager.zero, backward.admissionPolicy),
                "The virtual (Target, ZERO) pair must select the completed root terminal.\n$trace")
            val backwardRoot = f.results.single { it.runIndex == 2 }.analyzers.single { it.key == main }
            assertTrue(TargetSummary(f.manager.zero, Target.DemandTarget) in backwardRoot.outgoingTargets,
                "Paired C5 must retain the root result through static composition.\n$trace")
            val forward = f.configs.single { it.index == 3 }
            assertEquals(setOf(existingZeroAdmission(f.manager.zero)),
                forward.demand!!.initials(main, Reach.NORMAL, forward.admissionPolicy), trace)
            assertFalse(forward.demand.hasStaticCompletion, "Only run-1 to run-2 uses frozen static closure")
            assertTrue(report.entries.any { it.descriptor.rule.id == sink.rule.id }, trace)
        }
    }
}

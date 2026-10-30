package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.CallerRef
import kotlin.test.*

class StaticProducerGrammarTest {
    private fun demand(f: MethodAnalysisFixtures) =
        DemandStore.Builder(f.manager).build()

    /** The backward source result is created inside this method, without an
     * added-link query or a static sink seed which could validate it first. */
    private fun backwardSource(f: MethodAnalysisFixtures, condition: Pattern): RunMethodAnalyzer {
        val builder = RulePredicate.Builder(f.cancellation, f.manager.marks)
        val predicate = builder.build(builder.leaf(condition))
        val occurrence = RuleOccurrenceId(FormKey(FormOwner(), f.key.method, f.key, f.inst(0)),
            RuleKind.ENTRY_SOURCE, 0)
        val target = f.pattern(AccessPathBase.Argument(0), mark = MarkSlot.Concrete(f.mark("U")))
        val action = SourceAction(ActionId(occurrence, ActionRole.SOURCE, 0), target.fact)
        val summary = StatementSummary(setOf(STATIC), emptyList(), emptyList(), emptyMap(),
            sources = listOf(SourceRuleOccurrence(occurrence, predicate, listOf(action))))
        f.entryRules(RuleStatement(summary, StatementSummary.EMPTY, emptyList()))
        return f.core(f.config(index = 2, demand = demand(f)),
            localFactory = MethodLocalServicesFactory(::RunMethodLocalServices)).also {
            it.addInitial(f.manager.initial(target))
        }
    }

    @Test fun `a backward conditional source cannot execute a broad static result inside its method`() {
        for (root in listOf(true, false)) MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val condition = f.pattern(STATIC, if (root) emptyList() else listOf(cls), Tail.ANY)
            val actor = backwardSource(f, condition)
            val failure = assertFailsWith<IllegalStateException> { f.drain(actor) }
            assertContains(checkNotNull(failure.message), "Unsupported run-2 concrete static input")
            assertTrue(f.processed.none { it.facts.base == STATIC },
                "The unsupported result is diagnosed before it enters method work")
            assertTrue(actor.summaries.all().none { it.second.base == STATIC })
        }
    }

    @Test fun `backward source results keep exact class markers and bounded named fields`() {
        for (shape in 0..3) MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val field = f.field("f")
            val path = when (shape) {
                0 -> listOf(cls)
                3 -> listOf(cls, field, f.field("nested"))
                else -> listOf(cls, field)
            }
            val condition = f.pattern(STATIC, path, if (shape == 2) Tail.ANY else Tail.EXACT)
            val actor = backwardSource(f, condition)
            f.drain(actor)
            val leaves = actor.summaries.all().filter { it.second.base == STATIC }
                .flatMap { f.ops.leaves(it.second) }.toList()
            val expected = if (shape == 3) f.pattern(STATIC, listOf(cls, field), Tail.ANY,
                condition.fact.mark) else condition
            assertContains(leaves, expected)
        }
    }

    @Test fun `later forward named field results preserve MUST and field exclusion headers`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val path = listOf(cls, f.field("f"))
            val mark = MarkSlot.Concrete(f.mark("T"))
            val input = f.fact(STATIC, path, Tail.ANY_TAINT, mark,
                exclusion = ExclusionSet.of(f.field("excluded")))
            val actor = f.core(f.config(index = 3, demand = demand(f)))
            val premise = f.manager.initial(f.pattern(mark = mark))
            val bounded = ArrayList<Facts>()
            actor.cut(Cut.CALL, premise, input) { _, value -> bounded += value }
            assertEquals(listOf(input), bounded, "Current facts use anchor checks, not strict initial-header checks")
            actor.summaryDelta(premise, input)
            assertEquals(listOf(input), actor.summaries.all().map { it.second }.toList(),
                "Direct native/summary results keep their existing header too")
        }
    }
    @Test fun `same-prefix concrete static STAR demand selects the exact root at the next run2 call`() {
        for (hasNextDemand in listOf(true, false)) for (exclusionKind in 0..2) MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val mark = MarkSlot.Concrete(f.mark("T"))
            val exclusion = when (exclusionKind) {
                0 -> ExclusionSet.Empty
                1 -> ExclusionSet.of(f.field("excluded"))
                else -> ExclusionSet.of(intArrayOf(f.field("excluded"), f.field("other excluded")))
            }
            val entry = f.pattern(STATIC, path, Tail.STAR, mark, exclusion)
            val callee = f.store.key("next static consumer")
            val demand = DemandStore.Builder(f.manager).apply {
                add(f.key, DemandPattern(entry, entry))
                if (hasNextDemand) add(callee, DemandPattern(entry, entry))
            }.build()
            f.call(1, CallPlan(setOf(STATIC), listOf(CallStage.Callees(CallPoint.BEFORE,
                CallPoint.AFTER, listOf(callee))), emptyList(), CallPoint.BEFORE, CallPoint.AFTER))
            val config = f.config(index = 2, demand = demand)
            val owner = f.core(config, callFactory = MethodCallServicesFactory(::RunMethodCallServices))
            val next = f.core(config, key = callee)
            f.onSubscribe = { }
            f.onInitials = { event -> event.initials.forEach(next::addInitial) }
            val input = f.fact(STATIC, path, Tail.ANY, mark, layer = Layer.DEMAND)
            f.submitRestricted(owner, input)
            val exact = entry.copy(fact = entry.fact.copy(tail = Tail.EXACT), exclusion = ExclusionSet.Empty)
            assertEquals(listOf(f.manager.initial(exact)), owner.initials.all().toList())
            f.drain(owner)
            assertEquals(if (hasNextDemand) listOf(callee to listOf(f.manager.initial(exact))) else emptyList(),
                f.sentInitials.map { it.callee to it.initials }, "The caller sends final exact roots only when the target has demand")
            assertTrue(f.sentLinks.isEmpty(), "Restricted calls do not send raw inputs")
            assertEquals(if (hasNextDemand) listOf(f.manager.initial(exact)) else emptyList(),
                next.initials.all().toList(), "Accepted static inputs still need the callee's fixed demand")
            assertEquals(Tail.ANY, f.ops.leaves(input).single().fact.tail, "The supplied value remains unchanged")
        }
    }

    @Test fun `a valid run2 concrete STAR input cannot start without matching fixed demand`() {
        for (wrongMark in listOf(false, true)) MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val actual = f.pattern(STATIC, path, Tail.STAR, MarkSlot.Concrete(f.mark("T")),
                ExclusionSet.of(f.field("excluded")))
            val demand = DemandStore.Builder(f.manager).apply {
                if (wrongMark) {
                    val other = actual.copy(fact = actual.fact.copy(mark = MarkSlot.Concrete(f.mark("U"))))
                    add(f.key, DemandPattern(other, other))
                }
            }.build()
            val actor = f.core(f.config(index = 2, demand = demand))
            val input = f.fact(STATIC, path, Tail.STAR, actual.fact.mark, actual.exclusion, Layer.DEMAND)
            f.submitRestricted(actor, input)
            f.drain(actor)
            assertTrue(actor.initials.all().isEmpty())
            assertTrue(actor.summaries.all().none())
            assertTrue(f.sentLinks.isEmpty())
            assertEquals(listOf(actual), f.ops.leaves(input).toList())
        }
    }

    @Test fun `run2 concrete static input validation retains its geometry and tail rejections`() {
        MethodAnalysisFixtures().use { f ->
            val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
            val path = listOf(cls, f.field("f"))
            val excluded = ExclusionSet.of(f.field("excluded"))
            val bad = buildList {
                for (tail in listOf(Tail.EXACT, Tail.ANY, Tail.STAR)) add(f.pattern(STATIC, emptyList(), tail))
                for (tail in listOf(Tail.ANY, Tail.STAR)) add(f.pattern(STATIC, listOf(cls), tail))
                add(f.pattern(STATIC, listOf(cls), Tail.EXACT, exclusion = excluded))
                for (tail in listOf(Tail.EXACT, Tail.ANY)) add(f.pattern(STATIC, path, tail, exclusion = excluded))
                for (e in listOf(ExclusionSet.Empty, excluded)) add(f.pattern(STATIC, path, Tail.ANY_TAINT, exclusion = e))
            }
            for (input in bad) assertFailsWith<IllegalStateException>("Must reject $input") {
                validateRun2StaticFullInput(f.manager, input)
            }
            val marker = f.pattern(STATIC, listOf(cls), Tail.EXACT)
            assertFalse(validateRun2StaticFullInput(f.manager, marker), "The exact class marker is not a named field")
            assertTrue(f.processed.isEmpty())
        }
    }

    @Test fun `backward method inputs still reject a MUST fact before any initial starts`() {
        MethodAnalysisFixtures().use { f ->
            val path = listOf(f.manager.accessors.index(ClassStaticAccessor("C")), f.field("f"))
            val input = f.fact(STATIC, path, Tail.ANY_TAINT)
            val actor = f.core(f.config(index = 2, demand = demand(f)))
            assertFailsWith<IllegalStateException> {
                f.submitRestricted(actor, input)
            }
            assertTrue(actor.initials.all().isEmpty())
        }
    }
}

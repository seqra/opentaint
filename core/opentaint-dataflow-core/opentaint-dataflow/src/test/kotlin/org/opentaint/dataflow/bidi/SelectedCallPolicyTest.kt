package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.DemandStore
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*
import java.util.IdentityHashMap

/** Exercise the complete ordinary-call policy, including the real return pipeline. */
class SelectedCallPolicyTest {
    private val argument = AccessPathBase.Argument(0)
    private val result = AccessPathBase.Return
    private val calls = IdentityHashMap<RunMethodAnalyzer, RunMethodCallServices>()

    private fun install(f: MethodAnalysisFixtures, callee: MethodKey) {
        f.call(1, CallPlan(setOf(argument, result), listOf(
            CallStage.Callees(CallPoint.ADDED, CallPoint.RETURNED, listOf(callee)),
            CallStage.Edges(CallPoint.RETURNED, CallPoint.AFTER, StageKind.BIND_BACK,
                StatementSummary.identities(setOf(result))),
        ), emptyList(), CallPoint.ADDED, CallPoint.AFTER))
    }

    private fun actor(f: MethodAnalysisFixtures, demand: DemandStore): RunMethodAnalyzer =
        f.core(index = 3, demand = demand,
            callFactory = MethodCallServicesFactory { core ->
                RunMethodCallServices(core).also { calls[core] = it }
            })

    private fun offer(f: MethodAnalysisFixtures, actor: RunMethodAnalyzer, actual: Facts,
                      premise: PremiseKey = f.manager.zero) =
        checkNotNull(calls[actor]).process(EdgeDelta(premise, f.inst(1), actual))

    @Test
    fun `empty demand keeps saved replay on every offer and creates no current route`() {
        MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("callee")
            install(f, callee)
            val initial = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            f.records.add(Record(callee, Direction.FORWARD, initial,
                f.fact(result, tail = Tail.STAR, mark = MarkSlot.STAR)))
            val actor = actor(f, DemandStore.Builder(f.manager).build())
            val actual = f.fact(path = listOf(f.field("f")), mark = MarkSlot.Concrete(f.mark("T")))
            f.onSubscribe = { error("An empty demand cannot subscribe") }
            f.onInitials = { error("An empty demand cannot start initials") }
            repeat(2) { offer(f, actor, actual) }
            assertEquals(2L, actor.recordCrossings)
            val outputs = actor.edges.edgesAt(f.inst(1), f.manager.zero).flatMap {
                f.ops.leaves(it.second).toList()
            }.toList()
            assertEquals(listOf(PathFact(result, listOf(f.field("f")), Tail.EXACT,
                MarkSlot.Concrete(f.mark("T")))), outputs.map { it.fact })
            assertTrue(f.subscriptions.isEmpty())
            assertTrue(f.sentInitials.isEmpty())
            assertTrue(f.sentLinks.isEmpty())
        }
    }

    @Test
    fun `duplicate eligible offers still send complete initials while live replay admits one fresh delta`() {
        MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("callee")
            install(f, callee)
            val demand = DemandStore.Builder(f.manager).apply {
                add(callee, DemandPattern(f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR), null))
            }.build()
            val actor = actor(f, demand)
            val directory = CalleeSubscriptions(f.ops)
            var fresh = 0
            f.onSubscribe = { if (directory.admit(it) != null) fresh++ }
            f.onInitials = {}
            val actual = f.fact(path = listOf(f.field("f")), mark = MarkSlot.Concrete(f.mark("T")))
            repeat(2) { offer(f, actor, actual) }
            assertEquals(2, f.subscriptions.size)
            assertEquals(1, fresh)
            assertEquals(2, f.sentInitials.size)
            assertEquals(f.sentInitials[0].initials, f.sentInitials[1].initials)
            assertEquals(Tail.STAR, f.sentInitials[0].initials.single().tail)
            assertTrue(f.sentLinks.isEmpty())
            directory.clear()
        }
    }

    @Test
    fun `same emitted initial retains both actual suffixes in current summary application`() {
        MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("callee")
            install(f, callee)
            val field = f.field("f")
            val demand = DemandStore.Builder(f.manager).apply {
                add(callee, DemandPattern(f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR), null))
            }.build()
            val actor = actor(f, demand)
            val initial = f.manager.initial(f.pattern(path = listOf(field), tail = Tail.STAR, mark = MarkSlot.STAR))
            val pub = Publication(initial, f.fact(result, tail = Tail.STAR, mark = MarkSlot.STAR))
            f.onSubscribe = { part ->
                // The caller must install the live route before it starts the callee.
                assertTrue(f.sentInitials.size < f.subscriptions.size)
                val matched = assertNotNull(matches(part, pub, 0, f.ops, actor.mode))
                actor.applySummary(part.copy(added = matched), pub, 0)
            }
            f.onInitials = {}
            val actuals = listOf("a" to "T", "b" to "U").map { (child, mark) ->
                f.fact(path = listOf(field, f.field(child)), mark = MarkSlot.Concrete(f.mark(mark)))
            }
            actuals.forEach { offer(f, actor, it) }
            assertEquals(actuals, f.subscriptions.map { it.added })
            assertEquals(2, f.sentInitials.size)
            assertSame(f.sentInitials[0].initials.single(), f.sentInitials[1].initials.single())
            val outputs = actor.edges.edgesAt(f.inst(1), f.manager.zero).flatMap { f.ops.leaves(it.second).toList() }.toList()
            assertEquals(setOf(
                PathFact(result, listOf(f.field("a")), Tail.EXACT, MarkSlot.Concrete(f.mark("T"))),
                PathFact(result, listOf(f.field("b")), Tail.EXACT, MarkSlot.Concrete(f.mark("U"))),
            ), outputs.map { it.fact }.toSet())
        }
    }

    @Test
    fun `compatible current FLOW does not bypass an empty emission gate`() {
        MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("callee")
            install(f, callee)
            val demand = DemandStore.Builder(f.manager).apply {
                add(callee, DemandPattern(f.pattern(tail = Tail.ANY, mark = MarkSlot.STAR),
                    f.pattern(result, tail = Tail.ANY, mark = MarkSlot.STAR)))
            }.build()
            val actor = actor(f, demand)
            val initial = f.manager.initial(f.pattern(tail = Tail.STAR, mark = MarkSlot.STAR))
            val broad = f.fact(tail = Tail.STAR, mark = MarkSlot.STAR)
            val pub = Publication(initial, f.fact(result, tail = Tail.STAR, mark = MarkSlot.STAR))
            val part = Subscription(callee, org.opentaint.dataflow.bidi.store.CallerRef(f.key, initial,
                Layer.NORMAL, f.inst(1)), broad.layer, broad)
            assertNotNull(matches(part, pub, 0, f.ops, actor.mode))
            assertTrue(emitRestrictedInitials(actor.config, f.ops, callee, broad).isEmpty())
            f.onSubscribe = { actor.applySummary(it, pub, 0); fail("Empty demand subscribed") }
            f.onInitials = { fail("Empty demand started an initial") }
            offer(f, actor, broad, initial)
            assertTrue(f.subscriptions.isEmpty())
            assertTrue(actor.edges.edgesAt(f.inst(1)).none())
        }
    }

    @Test
    fun `rejected history is absent and accepted packed offer retains unrelated marks and protection`() {
        MethodAnalysisFixtures().use { f ->
            val callee = f.store.key("callee")
            install(f, callee)
            val t = MarkSlot.Concrete(f.mark("T"))
            val u = MarkSlot.Concrete(f.mark("U"))
            val field = f.field("f")
            val demand = DemandStore.Builder(f.manager).apply {
                add(callee, DemandPattern(f.pattern(tail = Tail.ANY, mark = t), null))
            }.build()
            val actor = actor(f, demand)
            val directory = CalleeSubscriptions(f.ops)
            val fresh = ArrayList<Facts>()
            f.onSubscribe = { directory.admit(it)?.let { accepted -> fresh += accepted.fresh.added } }
            f.onInitials = {}
            val rejected = f.fact(path = listOf(f.field("old")), mark = u)
            offer(f, actor, rejected)
            assertTrue(f.subscriptions.isEmpty())
            val packed = f.manager.mergeAddDelta(f.fact(path = listOf(field), mark = t),
                f.fact(path = listOf(field), mark = u)).first as TaintTree
            offer(f, actor, packed)
            offer(f, actor, packed.withProtection(packed.root))
            assertEquals(2, f.subscriptions.size)
            assertSame(packed, f.subscriptions.first().added)
            assertEquals(setOf(t, u), f.ops.leaves(f.subscriptions.last().added).map { it.fact.mark }.toSet())
            assertTrue(f.ops.leaves(f.subscriptions.last().added).all { it.fact.path == listOf(field) })
            assertEquals(2, fresh.size, "The protection-only upgrade must be fresh live work")
            assertNotNull((fresh.last() as TaintTree).nonSubsumable)
            assertEquals(2, f.sentInitials.size)
            directory.clear()
        }
    }
}

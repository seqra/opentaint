package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.engine.Target
import org.opentaint.dataflow.bidi.fixtures.EngineShellFixtures
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.Record
import kotlin.test.*

/** Terminal payloads use the same premise postings and register/replay protocol as AP rows. */
class TargetProtocolTest {
    @Test fun `AP and Target share a premise index without becoming each others result`() {
        val f = StoreFixtures()
        val index = PublicationIndex(f.manager, f.ops)
        val p = f.manager.initial(f.pattern())
        val target = TargetSummary(p, Target.NormalTarget(ReportId(4)))
        assertEquals(listOf(target), index.addTargets(listOf(target, target)))
        val part = Subscription(f.method, CallerRef(f.method, p, Layer.NORMAL, f.inst(1)), Layer.NORMAL, f.fact())
        val mode = ApMode(false, Direction.FORWARD, 2)
        assertTrue(index.candidates(part, mode).isEmpty())
        assertEquals(listOf(target to 0), index.targetCandidates(part, mode))
        val publication = Publication(p, f.fact(AccessPathBase.Return))
        assertEquals(listOf(publication), index.addAll(listOf(publication)))
        assertEquals(listOf(publication to 0), index.candidates(part, mode))
        assertEquals(listOf(target to 0), index.targetCandidates(part, mode))
        assertTrue(index.addTargets(listOf(target)).isEmpty())
    }

    @Test fun `Target index retains full ND premise and exact result identity`() {
        val f = StoreFixtures()
        val left = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
        val right = f.manager.initial(f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U"))))
        val full = f.manager.union(left, right)
        val index = PublicationIndex(f.manager, f.ops)
        val rows = listOf(TargetSummary(full, Target.NormalTarget(ReportId(1))),
            TargetSummary(full, Target.NormalTarget(ReportId(2))), TargetSummary(full, Target.DemandTarget))
        assertEquals(rows, index.addTargets(rows))
        val part = Subscription(f.method, CallerRef(f.method, left, Layer.NORMAL, f.inst(1)), Layer.NORMAL, f.fact())
        assertEquals(rows.map { it to 0 }, index.targetCandidates(part, ApMode(false, Direction.FORWARD, 2)))
        assertTrue(index.staticTargetCandidates().isEmpty())
    }

    @Test fun `static target candidates borrow the common premise postings`() {
        val f = StoreFixtures()
        val cls = f.manager.accessors.index(ClassStaticAccessor("C"))
        val p = f.manager.initial(f.pattern(STATIC, listOf(cls, f.field("value")), Tail.STAR))
        val index = PublicationIndex(f.manager, f.ops)
        val row = TargetSummary(p, Target.DemandTarget)
        index.addTargets(listOf(row))
        assertEquals(listOf(row to 0), index.staticTargetCandidates())
        assertTrue(index.staticCandidates().isEmpty())
    }

    private class Fixture : AutoCloseable {
        val f = EngineShellFixtures()
        val shared = f.shared()
        val events = ArrayDeque<RunEvent.TargetDelivery>()
        val replays = ArrayDeque<() -> Unit>()
        val notices = ArrayDeque<() -> Unit>()
        val targets = ArrayList<Pair<Subscription, TargetSummary>>()
        val staticTargets = ArrayList<Pair<Subscription, TargetSummary>>()
        var accept = true
        val config = f.config()
        val steps = object : ProtocolSteps {
            override fun replay(step: () -> Unit) { replays += step }
            override fun notify(step: () -> Unit) { notices += step }
        }
        val storage = SummaryStorage(f.a, f.manager, f.ops, steps)
        private val applier = object : SummaryApplier {
            override fun applySummary(part: Subscription, pub: Publication, member: Int) = error("No AP rows")
            override fun applyRecord(part: Subscription, record: Record) = error("No records")
            override fun applyRecordView(part: Subscription, view: RecordLeafView, nonSubsumable: Boolean) = error("No records")
            override fun applyTarget(part: Subscription, row: TargetSummary, member: Int) { targets += part to row }
            override fun applyStaticTarget(part: Subscription, row: TargetSummary, member: Int) { staticTargets += part to row }
        }
        val manager = SubscriptionManager(object : SubscriptionPort {
            override val config get() = this@Fixture.config
            override val ops get() = f.ops
            override val steps get() = this@Fixture.steps
            override fun summaryStorage(key: MethodKey) = storage
            override fun applier(key: MethodKey) = applier
            override fun post(event: RunEvent.Delivery): Boolean = error("No AP publication")
            override fun post(event: RunEvent.TargetDelivery): Boolean {
                if (accept) events += event
                return accept
            }
        })
        val initial = f.manager.initial(f.pattern())
        val part = Subscription(f.a, CallerRef(f.b, initial, Layer.NORMAL, f.inst(f.methodB, 1)), Layer.NORMAL, f.fact())
        val row = TargetSummary(initial, Target.NormalTarget(ReportId(10)))
        fun drain() {
            while (replays.isNotEmpty() || notices.isNotEmpty() || events.isNotEmpty()) {
                while (replays.isNotEmpty()) replays.removeFirst()()
                while (notices.isNotEmpty()) notices.removeFirst()()
                while (events.isNotEmpty()) events.removeFirst().let { manager.onTargetDelivery(it.callee, it.rows) }
            }
        }
        override fun close() { manager.freeze(); shared.close() }
    }

    @Test fun `publish before subscription is replayed and publish after registration is delivered`() {
        for (before in listOf(false, true)) Fixture().use { t ->
            if (before) t.storage.publishTargets(listOf(t.row))
            t.manager.subscribe(t.part)
            if (!before) t.storage.publishTargets(listOf(t.row))
            t.drain()
            assertTrue(t.targets.any { it.first == t.part && it.second == t.row })
            val count = t.targets.size
            repeat(3) { t.storage.publishTargets(listOf(t.row)); t.manager.subscribe(t.part) }
            t.drain()
            assertEquals(count, t.targets.size, "Owned publication and live input dedup remain in their existing owners")
        }
    }

    @Test fun `late input observes an already published Target and rejected required post fails`() = Fixture().use { t ->
        t.manager.subscribe(t.part)
        t.drain()
        t.accept = false
        t.storage.publishTargets(listOf(t.row))
        assertFails { t.notices.removeFirst()() }
        assertTrue(t.events.isEmpty())
        t.accept = true
        val other = t.part.copy(ref = t.part.ref.copy(call = t.f.inst(t.f.methodB, 2)))
        t.manager.subscribe(other)
        t.drain()
        assertTrue(t.targets.any { it.first.ref.call == other.ref.call && it.second == t.row })
    }
}

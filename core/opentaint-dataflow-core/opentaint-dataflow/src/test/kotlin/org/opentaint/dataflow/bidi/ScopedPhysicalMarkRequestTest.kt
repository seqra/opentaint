package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.store.BlockScope
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.bidi.store.RequestMarkSet
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

/** Physical callee requests return to the block which owns the caller input. */
class ScopedPhysicalMarkRequestTest {
    private val firstScope = BlockScope(BlockId(1), PortId(7))
    private val secondScope = BlockScope(BlockId(2), PortId(8))

    private class Harness : AutoCloseable {
        val f = PipelineFixtures()
        val sent = ArrayList<RunEvent>()
        private val notifications = ArrayDeque<RunEvent.ChangedRequests>()
        private val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY,
            listOf(f.caller), run1MarkMode = MarkMode.FULL)
        val manager = SubscriptionManager(object : SubscriptionPort by f.port {
            override val config get() = this@Harness.config
            override fun send(event: RunEvent): Boolean { sent += event; return true }
            override fun post(event: RunEvent.ChangedRequests): Boolean {
                notifications += event
                return true
            }
        })
        val calleeSlot = Run1Slot.Base(AccessPathBase.Argument(0))
        val callerSlot = Run1Slot.Base(AccessPathBase.Argument(1))
        val t = f.store.mark("T")
        val u = f.store.mark("U")
        val marks = RequestMarkSet.fromIds(intArrayOf(t.id, u.id))

        fun subscribe(scope: BlockScope, call: Int = 1, concrete: Boolean = false) {
            val original = if (concrete) f.ap.initial(callerSlot.base, null, Tail.EXACT,
                ExclusionSet.Empty, MarkSlot.Concrete(t)) else callerSlot.initial(f.ap)
            val actual = f.store.fact(calleeSlot.base,
                tail = if (concrete) Tail.EXACT else Tail.STAR,
                mark = if (concrete) MarkSlot.Concrete(t) else MarkSlot.STAR)
            val ref = CallerRef(f.caller, original, Layer.NORMAL, f.store.inst(call), scope = scope)
            manager.subscribe(Subscription(f.callee, ref, Layer.NORMAL, actual))
        }

        /** Use the real request-store commit and queued subscriber notification. */
        fun commit(method: MethodKey, slot: Run1Slot, selected: RequestMarkSet) {
            val temporary = RequestStorage().apply { addAll(slot, selected) }
            f.storage(method).commit(temporary)
        }

        fun deliverNotifications() {
            var delivered = 0
            while (notifications.isNotEmpty()) {
                check(++delivered < 100) { "Finite request notifications did not close" }
                val event = notifications.removeFirst()
                manager.onRequests(event.callee, event.rows)
            }
        }

        override fun close() { manager.freeze(); f.close() }
    }

    @Test fun `equal caller and slot in different block entries produce separate request batches`() {
        Harness().use { h ->
            h.subscribe(firstScope)
            h.subscribe(secondScope)
            h.commit(h.f.callee, h.calleeSlot, h.marks)
            assertTrue(h.sent.isEmpty(), "A publisher only queues the caller notification")
            h.deliverNotifications()
            val batches = h.sent.filterIsInstance<RunEvent.MarkRequestsIn>()
            assertEquals(2, batches.size,
                "The two block-owned original FLOW inputs are different request destinations")
            assertEquals(setOf(firstScope, secondScope), batches.map { it.scope }.toSet())
            assertTrue(batches.all { it.method == h.f.caller })
            assertTrue(batches.all { it.rows == mapOf<Run1Slot, RequestMarkSet>(h.callerSlot to h.marks) })
        }
    }

    @Test fun `a root request membership cannot suppress the same slot in a nonroot block`() {
        Harness().use { h ->
            val t = RequestMarkSet.of(h.t)
            h.commit(h.f.caller, h.callerSlot, t)
            assertTrue(h.f.storage(h.f.caller).borrowRequest(h.callerSlot).containsId(h.t.id))
            h.subscribe(firstScope)
            h.commit(h.f.callee, h.calleeSlot, t)
            h.deliverNotifications()
            val batches = h.sent.filterIsInstance<RunEvent.MarkRequestsIn>()
            assertEquals(1, batches.size,
                "Root R belongs to another abstraction; the nonroot FLOW supplier still needs T")
            assertEquals(h.f.caller, batches.single().method)
            assertEquals(firstScope, batches.single().scope)
            assertEquals(mapOf<Run1Slot, RequestMarkSet>(h.callerSlot to t), batches.single().rows)
        }
    }

    @Test fun `equal scoped destinations still merge across physical call sites`() {
        Harness().use { h ->
            h.subscribe(firstScope, call = 1)
            h.subscribe(firstScope, call = 2)
            h.commit(h.f.callee, h.calleeSlot, h.marks)
            h.deliverNotifications()
            val batches = h.sent.filterIsInstance<RunEvent.MarkRequestsIn>()
            assertEquals(1, batches.size, "Scope is part of the target; the call instruction is not")
            assertEquals(firstScope, batches.single().scope)
            assertEquals(mapOf<Run1Slot, RequestMarkSet>(h.callerSlot to h.marks), batches.single().rows)
        }
    }

    @Test fun `a directly supplied concrete answer still starts the physical callee root`() {
        Harness().use { h ->
            h.subscribe(firstScope, concrete = true)
            h.commit(h.f.callee, h.calleeSlot, RequestMarkSet.of(h.t))
            h.deliverNotifications()
            assertTrue(h.sent.none { it is RunEvent.MarkRequestsIn })
            val answer = h.sent.filterIsInstance<RunEvent.InitialAnswersIn>().single()
            assertEquals(h.f.callee, answer.method)
            val initial = answer.answers.single().initial
            assertEquals(h.calleeSlot.base, initial.base)
            assertEquals(Tail.EXACT, initial.tail)
            assertEquals(MarkSlot.Concrete(h.t), initial.mark)
        }
    }
}

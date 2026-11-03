package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.fixtures.PipelineFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class JoinedInputDetachmentTest {
    @Test fun `local detach moves current merged Facts and exact links without callbacks`() = MethodAnalysisFixtures().use { f ->
        val scope = BlockScope(BlockId(3), PortId(7))
        val parent = BlockScope(BlockId(1), PortId(8))
        val initial = f.manager.initial(f.pattern(AccessPathBase.Argument(1)))
        val link = LocalLink(parent, PortId(10), initial, Layer.NORMAL, scope)
        val actual = f.fact(AccessPathBase.LocalVar.create(9))
        var callbacks = 0
        val links = BlockSummaryLinks(f.ops, f.config().mode, scope,
            data = { _,_,_,_,_,_ -> callbacks++ }, terminal = { _,_,_ -> callbacks++ }, request = { _,_,_ -> callbacks++ })
        links.offer(link, actual)
        val before = ArrayList<Pair<LocalLink, Facts>>()
        links.forEachInput { l, v -> before += l to v }
        val joined = links.detachJoinedInputs()
        links.clear() // Release the live owner without changing the moved table.
        val after = ArrayList<Pair<LocalLink, Facts>>()
        joined.visit { l, v -> after += l to v }
        assertEquals(before, after)
        assertSame(before.single().second, after.single().second)
        assertSame(link, after.single().first)
        assertEquals(0, callbacks)
        assertFailsWith<IllegalStateException> { links.offer(link, actual) }
        assertFailsWith<IllegalStateException> { links.forEachInput { _,_ -> } }
        joined.close(); joined.close()
        assertFailsWith<IllegalStateException> { joined.visit { _,_ -> } }
        assertTrue(joined.javaClass.declaredFields.none { it.name == "this\$0" })
        assertTrue(LocalInputDirectory::class.java.declaredFields.none { kotlin.Function::class.java.isAssignableFrom(it.type) })
    }

    @Test fun `one physical input owner shared by callees is moved once with scope and fact identity`() = PipelineFixtures().use { f ->
        val second = f.store.key(context = "second-context")
        val scope = BlockScope(BlockId(6), PortId(12))
        val origin = f.ap.initial(f.store.pattern(AccessPathBase.Argument(1)))
        val actual = f.store.fact(AccessPathBase.Argument(0))
        val ref = CallerRef(f.caller, origin, Layer.NORMAL, f.store.inst(1), 4, scope)
        f.subscriptions.subscribe(Subscription(f.callee, ref, Layer.NORMAL, actual))
        f.subscriptions.subscribe(Subscription(second, ref, Layer.NORMAL, actual))
        val writer = Publication(f.ap.initial(f.store.pattern(AccessPathBase.Argument(0))), actual)
        val before = ArrayList<Subscription>()
        f.subscriptions.visitJoinedInputs(f.callee, writer, f.config.mode, before::add)
        val lease = JoinedBindingLease()
        lease.addCallers(f.storage(f.callee))
        lease.addCallers(f.storage(second)) // Same SubscriptionManager, already detached.
        f.subscriptions.freeze() // Cannot clear the moved table.
        val first = ArrayList<Subscription>(); val other = ArrayList<Subscription>()
        lease.visitCallerInputs(f.callee, writer, f.config.mode, first::add)
        lease.visitCallerInputs(second, writer, f.config.mode, other::add)
        assertEquals(before, first)
        assertSame(before.single().added, first.single().added)
        assertEquals(f.callee, first.single().callee)
        assertEquals(second, other.single().callee)
        assertSame(ref, first.single().ref)
        assertEquals(scope, first.single().ref.scope)
        assertEquals(4, first.single().ref.stageOrdinal)
        assertFailsWith<IllegalStateException> { f.storage(f.callee).candidates(first.single(), f.config.mode) }
        assertFailsWith<IllegalStateException> { f.subscriptions.subscribe(first.single()) }
        lease.close(); lease.close()
        assertFailsWith<IllegalStateException> { lease.visitCallerInputs(f.callee, writer, f.config.mode) {} }
    }

    @Test fun `detached physical ZERO-only input remains a genuine ZERO binding`() = PipelineFixtures().use { f ->
        val sub = f.subscription(Reach.NORMAL, f.ap.zero, zeroOnly = true)
        f.subscriptions.subscribe(sub)
        val lease = JoinedBindingLease()
        lease.addCallers(f.storage())
        val rows = ArrayList<Subscription>()
        lease.visitCallerInputs(f.callee, Publication(f.ap.zero, Reach.NORMAL), f.config.mode, rows::add)
        assertEquals(listOf(sub), rows)
        assertTrue(rows.single().zeroOnly)
        assertSame(Reach.NORMAL, rows.single().added)
        lease.close()
    }
}

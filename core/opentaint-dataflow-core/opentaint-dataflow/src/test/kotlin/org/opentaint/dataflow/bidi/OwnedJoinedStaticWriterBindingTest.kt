package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class OwnedJoinedStaticWriterBindingTest {
    private class Fixture : AutoCloseable {
        val f = MethodAnalysisFixtures()
        val ap = f.manager
        val keys = f.shared.staticWriteKeyInterner
        val mode = ApMode(true, Direction.FORWARD, 1)
        val c = listOf(ap.accessors.index(ClassStaticAccessor("C")), f.field("f"))
        val inputs = LinkedHashMap<OwnedScope, MutableList<OwnedWriterInput>>()
        val outputs = LinkedHashSet<Triple<OwnedScope, InitialAp, Pattern>>()
        fun flow(base: AccessPathBase) = ap.initial(f.pattern(base, tail = Tail.STAR, mark = MarkSlot.STAR))
        fun scope(block: Int, entry: Int) = BlockScope(BlockId(block), PortId(entry))
        fun local(owner: OwnedScope, parent: BlockScope, original: InitialAp, actual: Facts, point: Int) {
            val link = LocalLink(parent, PortId(point), original, actual.layer, owner.local)
            inputs.getOrPut(owner) { ArrayList() } += OwnedWriterInput.local(owner.method, link, actual)
        }
        fun call(callee: OwnedScope, caller: OwnedScope, original: InitialAp, actual: Facts, stage: Int = 0) {
            inputs.getOrPut(callee) { ArrayList() } += OwnedWriterInput.call(Subscription(callee.method,
                CallerRef(caller.method, original, actual.layer, f.inst(1), stage, caller.local), actual.layer, actual))
        }
        fun binder() = OwnedJoinedStaticWriterBinding(f.ops, mode, keys,
            borrow = { owner, _, visit -> inputs[owner].orEmpty().forEach(visit) },
            onBound = { owner, original, result -> outputs += Triple(owner, original, result) },
            checkpoint = f.cancellation::checkpoint)
        override fun close() = f.close()
    }

    @Test
    fun `local writer climbs enclosing scopes then a real caller scope before its root`() = Fixture().use { t ->
        val method = t.f.key
        val caller = t.f.store.key("caller")
        val child = OwnedScope(method, t.scope(5, 8))
        val middle = OwnedScope(method, t.scope(3, 4))
        val root = OwnedScope(method, BlockScope.ROOT)
        val callerLoop = OwnedScope(caller, t.scope(9, 2))
        val callerRoot = OwnedScope(caller, BlockScope.ROOT)
        val v = AccessPathBase.LocalVar.create(1)
        val x = AccessPathBase.LocalVar.create(2)
        val arg = AccessPathBase.Argument(0)
        val atom = MarkSlot.Concrete(t.f.mark("T"))
        t.local(child, middle.local, t.flow(x), t.f.fact(v, tail = Tail.STAR, mark = MarkSlot.STAR), 10)
        t.local(middle, root.local, t.flow(arg), t.f.fact(x, tail = Tail.STAR, mark = MarkSlot.STAR), 11)
        t.call(root, callerLoop, t.ap.zero, t.f.fact(arg, mark = atom), stage = 7)
        t.local(callerLoop, callerRoot.local, t.ap.zero, Reach.NORMAL, 12)
        val binder = t.binder()
        binder.offer(child, t.keys.intern(t.flow(v), t.f.pattern(STATIC, t.c, Tail.STAR, MarkSlot.STAR)))
        val statistics = binder.complete()
        assertEquals(5L, statistics.admittedWriters)
        assertEquals(statistics.admittedWriters, statistics.processedWriters)
        assertEquals(setOf(middle, root, callerLoop, callerRoot), t.outputs.map { it.first }.toSet())
        assertTrue(t.outputs.any { it.first == callerRoot && it.second.isZero && it.third.fact.mark == atom })
        assertFalse(t.outputs.any { it.first.method != method && it.first.method != caller })
    }

    @Test
    fun `equal writer keys in different entry scopes stay independent`() = Fixture().use { t ->
        val first = OwnedScope(t.f.key, t.scope(5, 8))
        val second = OwnedScope(t.f.key, t.scope(5, 9))
        val v = AccessPathBase.LocalVar.create(1)
        val a = t.flow(AccessPathBase.Argument(0))
        val b = t.flow(AccessPathBase.Argument(1))
        t.local(first, BlockScope.ROOT, a, t.f.fact(v, tail = Tail.STAR, mark = MarkSlot.STAR), 10)
        t.local(second, BlockScope.ROOT, b, t.f.fact(v, tail = Tail.STAR, mark = MarkSlot.STAR), 10)
        val row = t.keys.intern(t.flow(v), t.f.pattern(STATIC, t.c, Tail.STAR, MarkSlot.STAR))
        val binder = t.binder()
        binder.offer(first, row); binder.offer(second, row)
        val statistics = binder.complete()
        assertEquals(4L, statistics.admittedWriters)
        assertEquals(setOf(a, b), t.outputs.map { it.second }.toSet())
    }

    @Test
    fun `cyclic local input links terminate by owned writer membership without iteration keys`() = Fixture().use { t ->
        val owner = OwnedScope(t.f.key, t.scope(5, 8))
        val v = AccessPathBase.LocalVar.create(1)
        val initial = t.flow(v)
        t.local(owner, owner.local, initial, t.f.fact(v, tail = Tail.STAR, mark = MarkSlot.STAR), 10)
        val binder = t.binder()
        binder.offer(owner, t.keys.intern(initial, t.f.pattern(STATIC, t.c, Tail.STAR, MarkSlot.STAR)))
        val statistics = binder.complete()
        assertEquals(1L, statistics.admittedWriters)
        assertEquals(1L, statistics.processedWriters)
        assertEquals(1, t.outputs.size)
    }

    @Test
    fun `local ZERO writers require actual reached ZERO controls`() = Fixture().use { t ->
        val owner = OwnedScope(t.f.key, t.scope(5, 8))
        val wrong = t.ap.initial(t.f.pattern(AccessPathBase.Argument(0)))
        t.local(owner, t.scope(2, 3), t.ap.zero, Reach.NORMAL, 10)
        t.local(owner, t.scope(2, 4), wrong, Reach.NORMAL, 11)
        val binder = t.binder()
        binder.offer(owner, t.keys.intern(t.ap.zero, t.f.pattern(STATIC, t.c)))
        binder.complete()
        assertEquals(setOf(t.scope(2, 3)), t.outputs.map { it.first.local }.toSet())
        assertTrue(t.outputs.all { it.second.isZero })
    }

    @Test
    fun `static local original becomes a bridge without entering the writer queue`() = Fixture().use { t ->
        val owner = OwnedScope(t.f.key, t.scope(5, 8))
        val static = t.ap.initial(t.f.pattern(STATIC, t.c, Tail.STAR, MarkSlot.STAR))
        val v = AccessPathBase.LocalVar.create(1)
        t.local(owner, BlockScope.ROOT, static, t.f.fact(v, tail = Tail.STAR, mark = MarkSlot.STAR), 10)
        val binder = t.binder()
        binder.offer(owner, t.keys.intern(t.flow(v), t.f.pattern(STATIC, t.c, Tail.STAR, MarkSlot.STAR)))
        val statistics = binder.complete()
        assertEquals(1L, statistics.admittedWriters)
        assertSame(static, t.outputs.single().second)
    }
}

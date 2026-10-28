package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.driver.SeedIndex
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.MethodAnalysisFixtures
import org.opentaint.dataflow.bidi.store.CallerRef
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.TimeSource

class JoinedStaticWriterBindingTest {
    private class Fixture : AutoCloseable {
        val f = MethodAnalysisFixtures()
        val ap = f.manager
        val config = RunConfig(1, 1, null, f.records, SeedIndex.EMPTY, listOf(f.key), run1MarkMode = MarkMode.FULL)
        val stores = HashMap<MethodKey, SummaryStorage>()
        val keys = f.shared.staticWriteKeyInterner
        val path = listOf(ap.accessors.index(ClassStaticAccessor("C")), f.field("f"))
        val outputs = LinkedHashSet<Triple<MethodKey, InitialAp, Pattern>>()
        private val manager = SubscriptionManager(object : SubscriptionPort {
            override val config = this@Fixture.config
            override val ops = f.ops
            override val steps = ProtocolSteps.Inline
            override fun summaryStorage(key: MethodKey) = store(key)
            override fun applier(key: MethodKey): SummaryApplier = fail("Joined binding must not ask for a live applier")
            override fun post(event: RunEvent.Delivery): Boolean = fail("No joined publication")
            override fun post(event: RunEvent.ChangedRequests): Boolean = fail("No joined request")
            override fun send(event: RunEvent): Boolean = fail("No joined event")
        })
        fun store(key: MethodKey) = stores.getOrPut(key) { SummaryStorage(key, ap, f.ops, ProtocolSteps.Inline) }
        fun flow(base: AccessPathBase) = ap.initial(base, null, Tail.STAR, ExclusionSet.Empty, MarkSlot.STAR)
        fun bind(callee: MethodKey, caller: MethodKey, original: InitialAp, actual: Facts,
                 stage: Int = 0, zeroOnly: Boolean = false) {
            manager.subscribe(Subscription(callee,
                CallerRef(caller, original, actual.layer, f.inst(1), stage), actual.layer, actual, zeroOnly))
        }
        fun binder(checkpoint: () -> Unit = f.cancellation::checkpoint) = JoinedStaticWriterBinding(f.ops, config.mode, keys,
            borrow = { method, writer, visit -> stores[method]?.visitJoinedInputs(writer, config.mode, visit) },
            onBound = { method, original, output -> outputs += Triple(method, original, output) }, checkpoint = checkpoint)
        override fun close() { manager.freeze(); f.close() }
    }

    @Test fun `primitive writer bindings retain original stages and close recursive caller chains once`() = Fixture().use { t ->
        val leaf = t.f.store.key("leaf"); val wrapper = t.f.store.key("wrapper"); val root = t.f.store.key("root")
        val calleeArg = AccessPathBase.Argument(0); val wrapperArg = AccessPathBase.Argument(1)
        val formal = t.flow(calleeArg); val wrapperOriginal = t.flow(wrapperArg)
        val mark = t.f.mark("T")
        t.bind(leaf, wrapper, wrapperOriginal, t.f.fact(calleeArg, tail = Tail.STAR, mark = MarkSlot.STAR), stage = 4)
        t.bind(wrapper, root, t.ap.zero, t.f.fact(wrapperArg, mark = MarkSlot.Concrete(mark)), stage = 7)
        t.bind(wrapper, wrapper, wrapperOriginal, t.f.fact(wrapperArg, tail = Tail.STAR, mark = MarkSlot.STAR), stage = 9)
        val binder = t.binder()
        val output = t.f.pattern(STATIC, t.path, Tail.STAR, MarkSlot.STAR)
        val id = t.keys.intern(formal, output)
        binder.offer(leaf, id); binder.offer(leaf, id)
        val stats = binder.complete()
        assertEquals(3L, stats.admittedWriters)
        assertEquals(stats.admittedWriters, stats.processedWriters)
        assertTrue(t.outputs.any { it.first == wrapper && it.second === wrapperOriginal && it.third == output })
        assertTrue(t.outputs.any { it.first == root && it.second.isZero && it.third.fact.mark == MarkSlot.Concrete(mark) })
        assertTrue(t.stores.values.all { it.staticCandidates().isEmpty() }, "Guide binding publishes no summary")
    }

    @Test fun `ZERO writer uses only genuine reached ZERO call controls`() = Fixture().use { t ->
        val callee = t.f.store.key("source"); val good = t.f.store.key("good"); val wrong = t.f.store.key("wrong")
        val atom = t.f.mark("T")
        val wrongOrigin = t.ap.initial(t.f.pattern(AccessPathBase.Argument(0), mark = MarkSlot.Concrete(atom)))
        t.bind(callee, good, t.ap.zero, Reach.NORMAL, stage = 3)
        t.bind(callee, good, t.ap.zero, Reach.NORMAL, stage = 5, zeroOnly = true)
        t.bind(callee, wrong, wrongOrigin, Reach.NORMAL, stage = 6)
        val binder = t.binder()
        binder.offer(callee, t.keys.intern(t.ap.zero, t.f.pattern(STATIC, t.path, mark = MarkSlot.Concrete(atom))))
        binder.complete()
        assertEquals(setOf(good), t.outputs.map { it.first }.toSet())
        assertTrue(t.outputs.all { it.second.isZero })
    }

    @Test fun `complete callee context and concrete mark are checked before writer binding`() = Fixture().use { t ->
        val callee = t.f.store.key("callee"); val otherContext = t.f.store.key("same method other context")
        val right = t.f.store.key("right"); val wrong = t.f.store.key("wrong")
        val arg = AccessPathBase.Argument(0); val a = t.f.mark("T"); val b = t.f.mark("U")
        t.bind(otherContext, wrong, t.ap.zero, t.f.fact(arg, mark = MarkSlot.Concrete(a)))
        t.bind(callee, wrong, t.ap.zero, t.f.fact(arg, mark = MarkSlot.Concrete(b)))
        t.bind(callee, right, t.ap.zero, t.f.fact(arg, mark = MarkSlot.Concrete(a)), stage = 8)
        val initial = t.ap.initial(t.f.pattern(arg, mark = MarkSlot.Concrete(a)))
        val binder = t.binder()
        binder.offer(callee, t.keys.intern(initial, t.f.pattern(STATIC, t.path, mark = MarkSlot.Concrete(b))))
        binder.complete()
        assertEquals(setOf(right), t.outputs.map { it.first }.toSet())
        assertTrue(t.outputs.all { it.third.fact.mark == MarkSlot.Concrete(b) })
    }

    @Test fun `raw FLOW exclusions remain active until actual call application finishes`() = Fixture().use { t ->
        val callee = t.f.store.key("filtered"); val caller = t.f.store.key("caller")
        val arg = AccessPathBase.Argument(0); val a = t.f.mark("T"); val b = t.f.mark("U")
        val first = t.f.fact(arg, mark = MarkSlot.Concrete(a))
        val both = t.ap.mergeAddDelta(first, t.f.fact(arg, mark = MarkSlot.Concrete(b))).first
        t.bind(callee, caller, t.ap.zero, both)
        val excluded = MarkSlot.Star(MarkExclusions.of(t.ap.marks, a))
        val binder = t.binder()
        binder.offer(callee, t.keys.intern(t.flow(arg), t.f.pattern(STATIC, t.path, Tail.STAR, excluded)))
        binder.complete()
        assertEquals(setOf(MarkSlot.Concrete(b)), t.outputs.map { it.third.fact.mark }.toSet())
    }

    @Test fun `FLOW input keeps raw mx without replaying its already live exclusion request`() = Fixture().use { t ->
        val callee = t.f.store.key("flow excluded"); val caller = t.f.store.key("flow caller")
        val arg = AccessPathBase.Argument(0); val original = t.flow(AccessPathBase.Argument(1))
        val atom = t.f.mark("T")
        t.bind(callee, caller, original, t.f.fact(arg, tail = Tail.STAR, mark = MarkSlot.STAR))
        val excluded = MarkSlot.Star(MarkExclusions.of(t.ap.marks, atom))
        val binder = t.binder()
        binder.offer(callee, t.keys.intern(t.flow(arg), t.f.pattern(STATIC, t.path, Tail.STAR, excluded)))
        binder.complete()
        assertEquals(setOf<MarkSlot>(excluded), t.outputs.map { it.third.fact.mark }.toSet())
        assertTrue(t.outputs.single().second === original)
        // Fixture port fails if any request, event, applier or publication is used.
    }

    @Test fun `a static caller original becomes B without entering the writer queue`() = Fixture().use { t ->
        val callee = t.f.store.key("writer"); val caller = t.f.store.key("static caller")
        val arg = AccessPathBase.Argument(0)
        val staticOriginal = t.ap.initial(t.f.pattern(STATIC, t.path, Tail.STAR, MarkSlot.STAR))
        t.bind(callee, caller, staticOriginal, t.f.fact(arg, tail = Tail.STAR, mark = MarkSlot.STAR))
        val binder = t.binder()
        binder.offer(callee, t.keys.intern(t.flow(arg), t.f.pattern(STATIC, t.path, Tail.STAR, MarkSlot.STAR)))
        val stats = binder.complete()
        assertEquals(1L, stats.admittedWriters)
        assertTrue(t.outputs.single().second === staticOriginal)
    }

    @Test fun `independent deadline stops a joined CPU loop at ordinary AP cancellation checks`() {
        val cancellation = Cancellation()
        val started = TimeSource.Monotonic.markNow()
        var timedOut = false
        assertFailsWith<Cancellation.Cancelled> {
            withJoinedDeadline(remaining = { 25.milliseconds - started.elapsedNow() },
                onTimeout = { timedOut = true; cancellation.cancel() }) {
                while (true) cancellation.checkpoint()
            }
        }
        assertTrue(timedOut)
    }

    @Test fun `cancelled joined writer completion exports no bound keys`() = Fixture().use { t ->
        val binder = t.binder()
        val callee = t.f.store.key("callee")
        binder.offer(callee, t.keys.intern(t.flow(AccessPathBase.Argument(0)),
            t.f.pattern(STATIC, t.path, Tail.STAR, MarkSlot.STAR)))
        t.f.cancellation.cancel()
        assertFailsWith<Cancellation.Cancelled> { binder.complete() }
        assertTrue(t.outputs.isEmpty())
    }
}

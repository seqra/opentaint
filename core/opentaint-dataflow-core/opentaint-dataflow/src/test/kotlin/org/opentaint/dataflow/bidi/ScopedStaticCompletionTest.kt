package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.engine.BlockBoundaryDemandView
import org.opentaint.dataflow.bidi.engine.BlockEntryRole
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import kotlin.test.*

class ScopedStaticCompletionTest {
    private val fixture = StoreFixtures()
    private val ap = fixture.manager
    private val method = fixture.method
    private val block = BlockId(3)
    private val first = ScopedSummaryKey(method, BlockScope(block, PortId(10)), PortId(20))
    private val second = ScopedSummaryKey(method, BlockScope(block, PortId(11)), PortId(20))
    private val next = first.reversed().scope
    private val clazz = ap.accessors.index(ClassStaticAccessor("C"))
    private val f = fixture.field("f")
    private val g = fixture.field("g")
    private val t = MarkSlot.Concrete(fixture.mark("T"))
    private val u = MarkSlot.Concrete(fixture.mark("U"))
    private val x = AccessPathBase.LocalVar.create(4)
    private val ret = AccessPathBase.LocalVar.create(5)
    private fun c(field: Int, mark: MarkSlot = t) = fixture.pattern(STATIC, listOf(clazz, field), Tail.STAR, mark)
    private fun local(base: AccessPathBase, mark: MarkSlot = t) = fixture.pattern(base, mark = mark)

    private fun completion(): FrozenStaticCompletion = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
        addScopedSeed(first, local(x), c(f))
        addScopedSeed(first, c(f), local(ret))
        addScopedSeed(second, local(x, u), c(g, u))
        addScopedSeed(second, c(g, u), local(ret, u))
    }.build()

    @Test
    fun `scoped C2 unions actual exits but public method attachments remain separate`() {
        val frozen = completion()
        val owned = frozen.scopedViews().toMap()
        val scoped = assertNotNull(owned[OwnedScope(method, next)])
        assertEquals(1, owned.size)
        assertTrue(scoped.local(method).entries(local(ret)).any())
        assertTrue(scoped.local(method).entries(local(ret, u)).any())
        assertTrue(frozen.local(method).entries(local(ret)).none(), "Local registers must not leak into public method guidance")
        assertTrue(frozen.local(method).entries(local(ret, u)).none())
    }

    @Test
    fun `C5 selects one complete reversed control port pair`() {
        val frozen = completion()
        val scoped = frozen.scopedViews().toMap().getValue(OwnedScope(method, next))
        val demand = DemandStore.Builder(ap).also { it.withCompletion(method, next, scoped) }.build()
        val query = demand.scope(method, next)
        val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)
        val offered = fixture.fact(ret, tail = Tail.ANY, mark = t, layer = Layer.DEMAND)
        val starts = query.initials(offered, policy)
        assertTrue(starts.isNotEmpty())
        val original = starts.single().initial
        val raw = fixture.fact(x, mark = t, layer = Layer.DEMAND)
        assertTrue(query.intersect(PortId(10), original, raw, policy).isNotEmpty())
        assertTrue(query.intersect(PortId(11), original, raw, policy).isEmpty(),
            "The other entry's U permission cannot be mixed with this T row")
        assertTrue(query.intersect(PortId(99), original, raw, policy).isEmpty())
    }

    @Test
    fun `many scope views share one static bridge row and do not copy root local attachments`() {
        val builder = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY)
        builder.addSeed(method, local(AccessPathBase.Argument(0)), c(f))
        repeat(30) { index ->
            val producer = ScopedSummaryKey(method, BlockScope(BlockId(index + 1), PortId(10)), PortId(20))
            builder.addScopedBoundary(producer)
            builder.addScopedSeed(producer, c(f), c(g))
        }
        val frozen = builder.build()
        assertEquals(1, frozen.seedKeys)
        assertEquals(1L, frozen.seedMemberships)
        assertEquals(30, frozen.scopedViews().count())
        assertEquals(1L, frozen.writerAttachments, "The root attachment is stored once")
        for ((_, view) in frozen.scopedViews()) {
            assertTrue(view.local(method).incoming(c(g)).any { it.from == c(f) })
            assertTrue(view.local(method).incoming(c(f)).none { it.from.fact.base == AccessPathBase.Argument(0) })
        }
    }

    @Test
    fun `raw static shortcut and completed terminal reverse into distinct exact ports`() {
        val shortcut = ScopedSummaryKey(method, first.scope, PortId.STATIC_SHORTCUT)
        val terminal = shortcut.copy(exit = PortId.ROOT_EXIT)
        val frozen = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
            addScopedSeed(shortcut, ap.zero.toPattern(), c(f))
            addScopedTarget(terminal, c(f))
        }.build()
        val views = frozen.scopedViews().toMap()
        val raw = views.getValue(OwnedScope(method, BlockScope(block, PortId.STATIC_SHORTCUT)))
        val completed = views.getValue(OwnedScope(method, BlockScope(block, PortId.ROOT_EXIT)))
        assertTrue(raw.local(method).targetInputs().none(), "A raw write is not an already completed exit")
        assertTrue(raw.local(method).entries(c(f)).any())
        assertEquals(listOf(c(f)), completed.local(method).targetInputs().toList())
        assertTrue(completed.selectExit(PortId(10)).local(method).targetInputs().any())
        assertTrue(completed.selectExit(PortId(11)).local(method).targetInputs().none())
        assertEquals(PortId.STATIC_SHORTCUT, shortcut.reversed().scope.entry)
        assertEquals(PortId.ROOT_EXIT, terminal.reversed().scope.entry)
    }

    @Test
    fun `later demand snapshots do not inherit the run1 completion adapter`() {
        val frozen = completion()
        val scoped = frozen.scopedViews().toMap().getValue(OwnedScope(method, next))
        val firstRun = DemandStore.Builder(ap).also { it.withCompletion(method, next, scoped) }.build()
        assertTrue(firstRun.hasStaticCompletion)
        assertFailsWith<IllegalStateException> { firstRun.validateIncoming(3) }
        val later = DemandStore.Builder(ap).build()
        assertFalse(later.hasStaticCompletion)
        later.validateIncoming(3)
        val policy = RestrictedInitialPolicy(3, 2, Direction.FORWARD, ap.marks)
        assertTrue(later.scope(method, next).initials(fixture.fact(ret, mark = t), policy).isEmpty())
    }

    @Test
    fun `a frozen scope directory cannot grow when its builder is reused`() {
        val builder = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY)
        builder.addScopedBoundary(first)
        val frozen = builder.build()
        builder.addScopedBoundary(second.copy(scope = BlockScope(BlockId(7), PortId(11))))
        assertEquals(setOf(OwnedScope(method, next)), frozen.scopedViews().map { it.first }.toSet())
    }

    private fun shortcutDemand(vararg rows: Pair<ScopedSummaryKey, StaticGuidanceEdge>): DemandStore {
        val frozen = FrozenStaticCompletion.Builder(ap, DetachedStaticCallGraph.EMPTY).apply {
            for ((producer, row) in rows) addScopedSeed(producer, row.from, row.to)
        }.build()
        return DemandStore.Builder(ap).also { demand ->
            for ((owner, view) in frozen.scopedViews()) demand.withCompletion(owner.method, owner.local, view)
        }.build()
    }

    @Test
    fun `backward source Target uses its registered static write shortcut and exact paired output`() {
        val producer = first.copy(exit = PortId.STATIC_SHORTCUT)
        val demand = shortcutDemand(producer to StaticGuidanceEdge.of(ap.zero.toPattern(), c(f).copy(
            fact = c(f).fact.copy(tail = Tail.ANY))))
        val original=ap.initial(c(f)) // ANY selector starts an owned STAR identity.
        val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)
        assertTrue(demand.acceptsStaticShortcutTarget(method, block, first.scope.entry, original, policy))
        assertFalse(demand.acceptsStaticShortcutTarget(method, block, second.scope.entry, original, policy))
        assertFalse(demand.acceptsStaticShortcutTarget(method, BlockId(9), first.scope.entry, original, policy))
        assertFalse(demand.acceptsStaticShortcutTarget(method, block, first.scope.entry,
            ap.initial(c(f,u)),policy))
        assertFalse(demand.acceptsStaticShortcutTarget(method, block, first.scope.entry, ap.initial(local(x)), policy))
        assertFalse(demand.acceptsStaticShortcutTarget(method, block, first.scope.entry, original,
            RestrictedInitialPolicy(3, 2, Direction.FORWARD, ap.marks)))
        assertFalse(demand.acceptsStaticShortcutTarget(method, block, first.scope.entry, original,
            RestrictedInitialPolicy(4, 3, Direction.BACKWARD, ap.marks)))

        val physical = BlockScope(block, PortId(99))
        val normal = BlockScope(block, PortId.ROOT_EXIT)
        val view = BlockBoundaryDemandView(ap, demand.scope(method, physical), demand.scope(method, normal),
            Direction.BACKWARD, BlockEntryRole.NORMAL_INTERFACE, listOf(first.scope.entry)) { exit, initial, rule ->
            demand.acceptsStaticShortcutTarget(method, block, exit, initial, rule)
        }
        assertTrue(view.acceptsTarget(PortId.ROOT_ENTRY, original, policy))
        assertTrue(view.initials(fixture.fact(STATIC, listOf(clazz, f), Tail.ANY, t, layer = Layer.DEMAND), policy).isEmpty(),
            "The Target-result adapter does not add a DATA initial or alias the normal input scope")
        assertTrue(view.intersect(first.scope.entry, original, Reach.DEMAND, policy).isEmpty(),
            "Ordinary AP publication keeps its physical scope")
    }

    @Test
    fun `static shortcut Target requires a ZERO writer derivation rather than carry or arbitrary normal demand`() {
        val producer = first.copy(exit = PortId.STATIC_SHORTCUT)
        val original = ap.initial(c(f).copy(fact = c(f).fact.copy(tail = Tail.EXACT)))
        val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)
        val nonZeroWriter = shortcutDemand(producer to StaticGuidanceEdge.of(local(x), c(f)))
        assertFalse(nonZeroWriter.acceptsStaticShortcutTarget(method, block, first.scope.entry, original, policy))
        val completedWriter = shortcutDemand(producer.copy(exit = PortId.ROOT_EXIT) to
            StaticGuidanceEdge.of(ap.zero.toPattern(), c(f)))
        assertFalse(completedWriter.acceptsStaticShortcutTarget(method, block, first.scope.entry, original, policy),
            "An already completed normal endpoint must not authorize a raw write shortcut")
        val ordinaryOnly = DemandStore.Builder(ap).apply {
            withSharedStaticCarry()
            add(method, BlockScope(block, PortId.ROOT_EXIT), first.scope.entry,
                PairedDemand(DemandEntry.Data(c(f)), DemandExit.Zero))
        }.build()
        assertFalse(ordinaryOnly.acceptsStaticShortcutTarget(method, block, first.scope.entry, original, policy))
        assertTrue(ordinaryOnly.scope(method, BlockScope(block, PortId.ROOT_EXIT))
            .acceptsTarget(first.scope.entry, original, policy), "This control proves the excluded ordinary pair would match")
    }

    @Test
    fun `static shortcut Target reuses a registered W and lazy static bridge path without terminal authority`() {
        val producer = first.copy(exit = PortId.STATIC_SHORTCUT)
        val demand = shortcutDemand(
            producer to StaticGuidanceEdge.of(ap.zero.toPattern(), c(f)),
            producer to StaticGuidanceEdge.of(c(f), c(g)),
        )
        val original = ap.initial(c(g).copy(fact = c(g).fact.copy(tail = Tail.EXACT)))
        val policy = RestrictedInitialPolicy(2, 1, Direction.BACKWARD, ap.marks)
        assertTrue(demand.acceptsStaticShortcutTarget(method, block, first.scope.entry, original, policy))
        assertFalse(demand.acceptsStaticShortcutTarget(method, block, second.scope.entry, original, policy))
        val onlyBridge = shortcutDemand(producer to StaticGuidanceEdge.of(c(f), c(g)))
        assertFalse(onlyBridge.acceptsStaticShortcutTarget(method, block, first.scope.entry, original, policy))
    }
}

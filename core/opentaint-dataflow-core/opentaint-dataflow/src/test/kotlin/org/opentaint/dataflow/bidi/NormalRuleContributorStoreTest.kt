package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.engine.NormalRuleContributors
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import org.opentaint.dataflow.graph.BlockId
import org.opentaint.dataflow.graph.PortId
import org.opentaint.dataflow.util.Cancellation
import kotlin.test.*

class NormalRuleContributorStoreTest {
    private val f = StoreFixtures()
    private val normal = ApMode(false, Direction.FORWARD, 2)
    private val generation = FormOwner()
    private val occurrence = RuleOccurrenceId(FormKey(generation, f.commonMethod, f.method, f.inst(4)), RuleKind.CALL_SINK, 0)
    private val rule = NormalRuleDescriptor.predicate(occurrence)
    private fun site(stage: Int = 1, owner: FormOwner = FormOwner()): ResumeSite =
        ResumeSite.CallStageInput(OperationId(FormKey(owner, f.commonMethod, f.method, f.inst(4)), stage))
    private fun helper(store: NormalRuleContributorStore, scope: BlockScope = BlockScope.ROOT,
                       mode: ApMode = normal, method: MethodKey = f.method) =
        NormalRuleContributors(f.manager, store.snapshot(), method, scope, mode)
    private fun input(base: AccessPathBase = AccessPathBase.Argument(0), path: List<Int> = emptyList(),
                      layer: Layer = Layer.NORMAL): ConjunctionStore.Input {
        val pattern = f.pattern(base, path)
        return ConjunctionStore.Input(f.manager.initial(pattern), layer,
            f.manager.factsOf(pattern.fact, pattern.exclusion, layer))
    }
    private fun frozen(vararg entries: Pair<Int, ConjunctionStore.Input>): List<NormalRuleContributorRow> {
        val h = helper(NormalRuleContributorStore(f.manager))
        entries.forEach { (leaf, input) -> h.keep(rule, site(), leaf, input) }
        return h.freezeRows()
    }

    @Test fun `temporary inputs and later publications cannot enter an earlier run view`() {
        val store = NormalRuleContributorStore(f.manager)
        val old = helper(store)
        val producer = helper(store)
        assertTrue(producer.keep(rule, site(), 0, input()))
        val seen = ArrayList<NormalRuleContributorRow>()
        assertTrue(old.restoreOnce(rule, site(), seen::add))
        assertTrue(seen.isEmpty())
        assertEquals(0L, store.retainedRows)
        store.publish(producer.freezeRows())
        assertEquals(1L, store.retainedRows)
        assertFalse(old.restoreOnce(rule, site(), seen::add))
        assertTrue(seen.isEmpty(), "A run reads only its captured previous snapshot")
        val next = helper(store)
        assertTrue(next.restoreOnce(rule, site(), seen::add))
        assertEquals(1, seen.size)
        assertEquals(1L, next.restoredRows)
        assertFalse(next.restoreOnce(rule, site(), seen::add))
        assertEquals(1, seen.size)
    }

    @Test fun `normal-only capture keeps partial supports without requiring a completed cube`() {
        val store = NormalRuleContributorStore(f.manager)
        val h = helper(store)
        assertFalse(h.keep(rule, site(), 0, input(layer = Layer.DEMAND)))
        val wrongEffectiveLayer = input().copy(layer = Layer.DEMAND)
        assertFalse(h.keep(rule, site(), 0, wrongEffectiveLayer))
        val old = input()
        assertTrue(h.keep(rule, site(), 0, old))
        assertFalse(h.keep(rule, site(), 0, old))
        assertEquals(1L, h.capturedRows)
        assertEquals(0L, h.capturedUpdates)
        val rows = h.freezeRows()
        assertEquals(1, rows.size)
        assertSame(old.premise, rows.single().input.premise)
        assertSame(old.facts, rows.single().input.facts)
        store.publish(rows)
        assertEquals(1L, store.retainedRows)
    }

    @Test fun `full multi-premise origin and exact geometry stay in the accepted leaf`() {
        val first = f.manager.initial(f.pattern(AccessPathBase.Argument(0)))
        val second = f.manager.initial(f.pattern(AccessPathBase.Argument(1), mark = MarkSlot.Concrete(f.mark("U"))))
        val complete = f.manager.union(first, second)
        val field = f.field("f")
        val exclusion = ExclusionSet.of(f.field("blocked"))
        val checked = f.fact(AccessPathBase.This, listOf(field), Tail.ANY_TAINT,
            exclusion = exclusion) as TaintTree
        val store = NormalRuleContributorStore(f.manager)
        store.publish(frozen(1 to ConjunctionStore.Input(complete, Layer.NORMAL, checked)))
        val restored = ArrayList<NormalRuleContributorRow>()
        helper(store).restoreOnce(rule, site(), restored::add)
        val accepted = restored.single().input
        assertSame(complete, accepted.premise)
        assertEquals(setOf(first, second), accepted.premise.members.toSet())
        assertSame(checked, accepted.facts)
        val retained = assertIs<TaintTree>(accepted.facts)
        assertEquals(exclusion, retained.exclusion)
        assertEquals(Tail.ANY_TAINT, retained.anyTail)
    }

    @Test fun `equal geometry retains both protection classes in contributor snapshots`() {
        val store = NormalRuleContributorStore(f.manager)
        val plainInput = input()
        val plain = plainInput.facts as TaintTree
        val protected = plain.withProtection(plain.root, f.cancellation)
        assertNotEquals(plain, protected)
        store.publish(frozen(0 to plainInput))
        val earlier = store.snapshot()
        assertTrue(store.publish(frozen(0 to plainInput.copy(facts = protected))))
        assertEquals(2L, store.retainedRows)
        assertNull((earlier.allRows().single().input.facts as TaintTree).nonSubsumable)
        assertEquals(setOf(plain, protected), store.snapshot().allRows().map { it.input.facts }.toSet())
        assertFalse(store.publish(frozen(0 to plainInput)))
        assertEquals(setOf(plain, protected), store.snapshot().allRows().map { it.input.facts }.toSet())
    }

    @Test fun `checked trees merge only within the same leaf origin and group`() {
        val store = NormalRuleContributorStore(f.manager)
        val h = helper(store)
        val origin = input().premise
        val a = f.fact(path = listOf(f.field("a")))
        val b = f.fact(path = listOf(f.field("b")))
        assertTrue(h.keep(rule, site(), 0, ConjunctionStore.Input(origin, Layer.NORMAL, a)))
        assertTrue(h.keep(rule, site(), 0, ConjunctionStore.Input(origin, Layer.NORMAL, b)))
        assertTrue(h.keep(rule, site(), 1, ConjunctionStore.Input(origin, Layer.NORMAL, b)))
        assertEquals(2L, h.capturedRows)
        assertEquals(1L, h.capturedUpdates)
        store.publish(h.freezeRows())
        val rows = store.snapshot().allRows()
        assertEquals(2, rows.size)
        assertEquals((f.ops.leaves(a) + f.ops.leaves(b)).toSet(),
            f.ops.leaves(checkNotNull(rows.single { it.leaf == 0 }.input.facts)).toSet())
        assertEquals(f.ops.leaves(b).toSet(), f.ops.leaves(checkNotNull(rows.single { it.leaf == 1 }.input.facts)).toSet())
    }

    @Test fun `publication swaps one completed root and does not leak an earlier successful row on failure`() {
        val store = NormalRuleContributorStore(f.manager)
        val base = frozen(0 to input())
        store.publish(base)
        val earlier = store.snapshot()
        val additions = frozen(1 to input(AccessPathBase.Argument(1)), 2 to input(AccessPathBase.Argument(2)))
        val failing = sequence<NormalRuleContributorRow> {
            yield(additions.first())
            error("failed publication")
        }.asIterable()
        assertFailsWith<IllegalStateException> { store.publish(failing) }
        assertEquals(earlier.allRows(), store.snapshot().allRows())
        assertEquals(1L, store.retainedRows)
        val cancelled = sequence {
            yield(additions.first())
            f.cancellation.cancel()
            yield(additions.last())
        }.asIterable()
        assertFailsWith<Cancellation.Cancelled> { store.publish(cancelled) }
        f.cancellation.activate()
        assertEquals(earlier.allRows(), store.snapshot().allRows())
        store.publish(additions)
        assertEquals(3L, store.retainedRows)
        assertEquals(1L, earlier.retainedRows)
    }

    @Test fun `rule method port boundary phase and mode isolate snapshots`() {
        val store = NormalRuleContributorStore(f.manager)
        store.publish(frozen(0 to input()))
        val rows = ArrayList<NormalRuleContributorRow>()
        val anotherRule = NormalRuleDescriptor.predicate(occurrence.copy(ordinal = 1))
        helper(store).restoreOnce(anotherRule, site(), rows::add)
        helper(store, BlockScope(BlockId(3), PortId(7))).restoreOnce(rule, site(), rows::add)
        helper(store, method = f.key("other context")).restoreOnce(rule, site(), rows::add)
        helper(store).restoreOnce(rule, ResumeSite.BoundaryInput(site().operation, false), rows::add)
        assertTrue(rows.isEmpty())
        for (mode in listOf(ApMode(false, Direction.BACKWARD, 2),
            ApMode(true, Direction.FORWARD, 1, MarkMode.GROUP))) {
            val disabled = helper(store, mode = mode)
            assertFalse(disabled.keep(rule, site(), 0, input()))
            assertFalse(disabled.restoreOnce(rule, site(), rows::add))
            assertTrue(disabled.freezeRows().isEmpty())
        }
        assertTrue(rows.isEmpty())
        helper(store).restoreOnce(rule, site(), rows::add)
        assertEquals(1, rows.size)
    }

    @Test fun `site normalization removes runtime owners and unifies only the semantic sink BOUND point`() {
        assertEquals(NormalRuleContributors.stableSite(rule, site(1)),
            NormalRuleContributors.stableSite(rule, site(8)))
        val source = NormalRuleDescriptor.predicate(occurrence.copy(kind = RuleKind.CALL_SOURCE))
        assertNotEquals(NormalRuleContributors.stableSite(source, site(1)),
            NormalRuleContributors.stableSite(source, site(8)))
        assertEquals(NormalRuleContributors.stableSite(source, site(1, FormOwner())),
            NormalRuleContributors.stableSite(source, site(1, FormOwner())))
        val operation = site(1).operation
        assertNotEquals(NormalRuleContributors.stableSite(source, ResumeSite.BoundaryInput(operation, true)),
            NormalRuleContributors.stableSite(source, ResumeSite.BoundaryInput(operation, false)))
        assertNotEquals(NormalRuleContributors.stableSite(source, ResumeSite.CleanerInput(operation, 0, CleanerPhase.READ)),
            NormalRuleContributors.stableSite(source, ResumeSite.CleanerInput(operation, 0, CleanerPhase.WRITE)))
        val nested = ResumeSite.ReadOutput(operation, ResumeSite.BoundaryInput(operation, true))
        val otherNested = ResumeSite.ReadOutput(operation, ResumeSite.BoundaryInput(operation, false))
        assertNotEquals(NormalRuleContributors.stableSite(source, nested), NormalRuleContributors.stableSite(source, otherNested))
        assertNotEquals(NormalRuleContributors.stableSite(source, ResumeSite.StatementInput(operation)),
            NormalRuleContributors.stableSite(source, ResumeSite.StatementInput(operation.copy(substep = 1))))
        val action = ActionId(occurrence, ActionRole.SOURCE, 0)
        assertNotEquals(NormalRuleContributors.stableSite(source, ResumeSite.StatementInput(operation)),
            NormalRuleContributors.stableSite(source, ResumeSite.StatementInput(operation.copy(action = action))))
    }

    @Test fun `legacy value descriptors own their field shapes and distinguish sink alternatives`() {
        val field = f.field("f")
        val path = mutableListOf(field)
        val literal = f.pattern(path = path)
        val other = f.pattern(AccessPathBase.Argument(1))
        val target = f.pattern(AccessPathBase.Return, path = path).fact
        val edge = ConjunctiveEdge(listOf(literal, other), target)
        val key = NormalRuleDescriptor.legacyConjunction(edge)
        val equal = NormalRuleDescriptor.legacyConjunction(ConjunctiveEdge(
            listOf(f.pattern(path = listOf(field)), other), target.copy(path = listOf(field))))
        assertEquals(equal, key)
        val hash = key.hashCode()
        path += f.field("g")
        assertEquals(hash, key.hashCode())
        assertEquals(equal, key)
        val sink = localSink(listOf(literal, other))
        assertNotEquals(NormalRuleDescriptor.legacySink(sink),
            NormalRuleDescriptor.legacySink(localSink(sink.patterns, alternative = 1, rule = sink.rule)))
        val legacy = NormalRuleDescriptor.legacySink(sink)
        assertEquals(NormalRuleContributors.stableSite(legacy, site(1)),
            NormalRuleContributors.stableSite(legacy, site(8)))
    }

    @Test fun `freeze releases the reader and temporary batch and rejects later actor calls`() {
        val h = helper(NormalRuleContributorStore(f.manager))
        h.keep(rule, site(), 0, input())
        f.cancellation.cancel()
        val rows = h.freezeRows()
        assertEquals(1, rows.size, "Cleanup snapshots do not checkpoint cancellation")
        f.cancellation.activate()
        assertFailsWith<IllegalStateException> { h.restoreOnce(rule, site()) {} }
        assertFailsWith<IllegalStateException> { h.keep(rule, site(), 0, input()) }
    }
}

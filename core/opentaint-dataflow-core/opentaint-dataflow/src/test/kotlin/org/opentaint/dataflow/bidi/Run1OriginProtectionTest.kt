package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.fixtures.StoreFixtures
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.store.*
import kotlin.test.*

class Run1OriginProtectionTest {
    private val f = StoreFixtures()
    private val m = f.manager
    private val node = f.inst(1)
    private val t = f.mark("T")
    private val u = f.mark("U")
    private val v = f.mark("Fresh")
    private val rule = RuleOccurrenceId(FormKey(FormOwner(), f.commonMethod, f.method, node), RuleKind.CALL_SOURCE, 0)
    private fun pattern(index: Int, mark: TaintMark) = f.pattern(base = AccessPathBase.Argument(index), mark = MarkSlot.Concrete(mark))
    private fun initial(index: Int, mark: TaintMark = v) = m.initial(pattern(index, mark))
    private fun input(index: Int, mark: TaintMark, origin: InitialAp = initial(index), protected: Boolean = false): ConjunctionStore.Input {
        val plain = f.fact(base = AccessPathBase.Argument(index), mark = MarkSlot.Concrete(mark), layer = Layer.DEMAND) as TaintTree
        return ConjunctionStore.Input(origin, plain.layer, if (protected) plain.withProtection(plain.root) else plain)
    }
    private fun predicate(left: TaintMark, right: TaintMark): RulePredicate {
        val builder = RulePredicate.Builder(f.cancellation)
        return builder.build(builder.and(listOf(builder.leaf(pattern(0, left)), builder.leaf(pattern(1, right)))))
    }

    @Test fun `predicate contribution protection upgrade revisits all fixed origins once`() {
        val store = Run1OriginPredicateStore(m)
        val p = predicate(t, u)
        val seen = arrayListOf<Pair<InitialAp, Boolean>>()
        fun add(slot: Int, value: ConjunctionStore.Input) = store.add(rule, node, p,
            p.leaves.indexOf(pattern(slot, if (slot == 0) t else u)), value) { cube ->
            cube.emitProtectedOrigins("assign V", v) { i, flag -> seen += i to flag }
        }
        add(0, input(0, t))
        add(1, input(1, u))
        assertEquals(setOf(initial(0) to true, initial(1) to true), seen.toSet(), "V origins form local V-to-other-to-V cycles")
        // Use a different action mark to isolate ordinary false -> true contribution upgrades.
        val q = predicate(t, u)
        val otherStore = Run1OriginPredicateStore(m)
        val a = initial(0, t)
        val b = initial(1, t)
        val events = arrayListOf<Pair<InitialAp, Boolean>>()
        fun offer(slot: Int, value: ConjunctionStore.Input) = otherStore.add(rule, node, q,
            q.leaves.indexOf(pattern(slot, if (slot == 0) t else u)), value) { cube ->
            cube.emitProtectedOrigins("assign V", v) { i, flag -> events += i to flag }
        }
        offer(0, input(0, t, a))
        offer(1, input(1, u, b))
        assertEquals(setOf(a to false, b to false), events.toSet())
        events.clear()
        offer(0, input(0, t, a, protected = true))
        assertEquals(setOf(a to true, b to true), events.toSet())
        events.clear()
        offer(0, input(0, t, a, protected = true))
        assertTrue(events.isEmpty())
    }

    @Test fun `predicate uses selected triggering marks and original cycle separately`() {
        val store = Run1OriginPredicateStore(m)
        val p = predicate(u, v)
        val a = initial(0, t)
        val b = initial(1, u)
        val out = arrayListOf<Pair<InitialAp, Boolean>>()
        fun add(slot: Int, value: ConjunctionStore.Input) = store.add(rule, node, p,
            p.leaves.indexOf(pattern(slot, if (slot == 0) u else v)), value) { cube ->
            cube.emitProtectedOrigins("assign T", t) { i, flag -> out += i to flag }
        }
        // T in this packed input is not a selected literal contribution.
        val acceptedU = input(0, u, a)
        val strayT = input(0, t, a).facts as TaintTree
        val checked = acceptedU.facts as TaintTree
        val packed = m.taintTree(checked.base, checked.layer, m.taintAlg.mergeAdd(checked.root, strayT.root))
        add(0, acceptedU.copy(facts = packed))
        add(1, input(1, v, b))
        assertEquals(setOf(a to true, b to false), out.toSet())
    }

    @Test fun `conjunction late contribution flag updates all origins once and retains all ZERO test`() {
        val store = Run1OriginConjunctionStore(m)
        val key = Any()
        val a = initial(0, t)
        val b = initial(1, t)
        val out = arrayListOf<Pair<InitialAp, Boolean>>()
        fun offer(slot: Int, value: ConjunctionStore.Input) = store.addProtectedOrigins(key, node, 2, slot,
            value, v, if (slot == 0) t else u) { i, _, flag -> out += i to flag }
        offer(0, input(0, t, a))
        offer(1, input(1, u, b))
        assertEquals(setOf(a to false, b to false), out.toSet())
        out.clear()
        offer(0, input(0, t, a, protected = true))
        assertEquals(setOf(a to true, b to true), out.toSet())
        out.clear()
        offer(0, input(0, t, a, protected = true))
        assertTrue(out.isEmpty())
        offer(0, input(0, t, m.zero))
        assertTrue(out.none { it.first.isZero })
        offer(1, input(1, u, m.zero))
        assertEquals(listOf(m.zero to false), out.filter { it.first.isZero })
    }

    @Test fun `same selected mark assignment protects every contributing origin`() {
        val store = Run1OriginConjunctionStore(m)
        val out = arrayListOf<Pair<InitialAp, Boolean>>()
        val key = Any()
        store.addProtectedOrigins(key, node, 2, 0, input(0, t), t, t) { i, _, flag -> out += i to flag }
        store.addProtectedOrigins(key, node, 2, 1, input(1, u), t, u) { i, _, flag -> out += i to flag }
        assertEquals(setOf(initial(0) to true, initial(1) to true), out.toSet())
    }
}

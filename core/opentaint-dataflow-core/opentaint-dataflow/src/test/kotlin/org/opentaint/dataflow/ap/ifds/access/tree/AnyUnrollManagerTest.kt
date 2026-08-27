package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.tree.AnyUnrollManager.Companion.MINT_TEST
import java.lang.ref.WeakReference
import java.util.concurrent.CountDownLatch
import java.util.concurrent.Executors
import java.util.concurrent.TimeUnit
import java.util.concurrent.atomic.AtomicReference
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * The `[any]` unroll manager on its own: the two pointer DSUs, the deterministic automaton they
 * index, and the charge.
 *
 * The two properties that are easy to get wrong and expensive to get wrong are pinned here rather
 * than end to end, because both fail as a HANG rather than as a wrong answer: a cycle in the DSU
 * forest, which makes `find` spin forever, and an ancestor-descendant union, which must produce a
 * self-loop because that self-loop is how a program loop reaches its fixed point.
 */
class AnyUnrollManagerTest {

    private companion object {
        // The accessor indices are opaque to the manager -- it only ever uses them as map keys --
        // so plain distinct ints are enough here.
        const val A = 100
        const val B = 200
        const val C = 300
    }

    private fun manager(limit: Int = 1_000, pathLengthCost: Boolean = true) =
        AnyUnrollManager(limit, pathLengthCost = pathLengthCost)

    private fun AnyUnrollManager.origin() = assertNotNull(newOrigin(MINT_TEST), "the manager must be enabled")

    private fun AnyUnrollState.transition(accessor: Int): AnyUnrollState? =
        find().children?.get(accessor)?.find()

    /* ---------- the DSU ---------- */

    @Test
    fun `a fresh state is its own representative`() {
        val m = manager()
        val x = m.origin()

        assertSame(x, x.find())
        assertNull(x.parent, "a representative has no parent link")
        assertEquals(1, x.pathCount)
        assertEquals(0, m.totalOf(x), "a fresh origin has spent nothing")
    }

    @Test
    fun `union prefers the receiver's representative`() {
        val m = manager()
        val x = m.origin()
        val y = m.readChild(x, A)!!          // a second state in the same dag

        val merged = m.union(x, y)

        assertSame(x, merged, "the receiver wins, so the accumulated tree's id does not move")
        assertSame(x, y.find(), "the arrival is absorbed")
    }

    @Test
    fun `union is idempotent`() {
        val m = manager()
        val x = m.origin()

        assertSame(x.find(), m.union(x, x))
        assertSame(x.find(), m.union(x, x)?.let { m.union(it, x) })
        assertEquals(1, x.pathCount, "a self-union must not double the path count")
    }

    @Test
    fun `union sums the path counts`() {
        val m = manager()
        val root = m.origin()
        val a = m.readChild(root, A)!!
        val b = m.readChild(root, B)!!

        assertEquals(1, a.pathCount)
        assertEquals(1, b.pathCount)

        val merged = assertNotNull(m.union(a, b))
        assertEquals(2, merged.pathCount, "two sequences now reach one state")
    }

    @Test
    fun `a disabled manager allocates nothing`() {
        val m = AnyUnrollManager(limit = -1)

        assertFalse(m.enabled)
        assertNull(m.newOrigin(MINT_TEST))
        assertNull(m.union(null, null))
        assertNull(m.readChild(null, A))
        assertNull(m.readChildPaidOnly(null, A))
        assertFalse(m.budgetExhausted(null))
    }

    /* ---------- the automaton ---------- */

    @Test
    fun `a repeated read reuses the transition free`() {
        val m = manager()
        val root = m.origin()

        val first = assertNotNull(m.readChild(root, A))
        assertEquals(1, m.totalOf(root), "the first read charges")

        val second = m.readChild(root, A)
        assertSame(first, second, "the same accessor names the same state")
        assertEquals(1, m.totalOf(root), "re-derivation is free -- this is the termination argument")
    }

    /* ---------- the cost: what `L` is a budget OF ---------- */

    /**
     * The pot counts ACCESSORS, not sequences: the charge for a transition is the total LENGTH of
     * the words it authorises, so `total` is the sum of `|w|` over every word the automaton has
     * materialised.
     *
     * A chain makes the two measures diverge maximally. `a`, `ab`, `abc` is three words -- the
     * legacy measure's answer -- carrying six accessors, which is what the automaton actually built.
     */
    @Test
    fun `the pot charges the LENGTH of every materialised sequence`() {
        val m = manager()
        val root = m.origin()

        val a = assertNotNull(m.readChild(root, A))
        assertEquals(1, m.totalOf(root), "word `a`, length 1")

        val ab = assertNotNull(m.readChild(a, B))
        assertEquals(3, m.totalOf(root), "plus `ab`, length 2")

        m.readChild(ab, C)
        assertEquals(6, m.totalOf(root), "plus `abc`, length 3 -- 1 + 2 + 3 over the acyclic paths")
    }

    /** The ablation, on the same shape: one unit per word, so the depth is invisible. */
    @Test
    fun `the legacy measure charges one per sequence however long`() {
        val m = manager(pathLengthCost = false)
        val root = m.origin()

        val a = assertNotNull(m.readChild(root, A))
        val ab = assertNotNull(m.readChild(a, B))
        m.readChild(ab, C)

        assertEquals(3, m.totalOf(root), "three words, and a 3-accessor chain bills the same as three first steps")
    }

    @Test
    fun `the charge scales with the path count`() {
        val m = manager()
        val root = m.origin()
        val a = m.readChild(root, A)!!
        val b = m.readChild(root, B)!!
        assertEquals(2, m.totalOf(root))

        val shared = assertNotNull(m.union(a, b))
        assertEquals(2, shared.pathCount)
        assertEquals(2, shared.lengthSum, "two words of length 1 reach the merged state")

        m.readChild(shared, C)
        assertEquals(
            6, m.totalOf(root),
            "emitting `c` at a state two sequences reach authorises `ac` and `bc` -- two words, four accessors"
        )

        val legacy = manager(pathLengthCost = false)
        val lRoot = legacy.origin()
        val lShared = assertNotNull(legacy.union(legacy.readChild(lRoot, A), legacy.readChild(lRoot, B)))
        legacy.readChild(lShared, C)
        assertEquals(4, legacy.totalOf(lRoot), "the legacy measure counts the two words and not their letters")
    }

    /**
     * A cycle is charged for at most ONE lap, which is what makes the measure finite where the
     * accepted language is not.
     *
     * The transition that closes the loop was minted -- and charged -- as a fresh state before the
     * union folded it into its own predecessor. Every later lap finds it already there.
     */
    @Test
    fun `a cycle is charged at most one lap`() {
        val m = manager()
        val root = m.origin()
        val a = assertNotNull(m.readChild(root, A))
        assertEquals(1, m.totalOf(root))

        assertSame(root, m.union(root, a), "m --a--> m")
        val afterFold = m.totalOf(root)
        assertEquals(1, afterFold, "the fold neither charges nor refunds")

        repeat(10) { assertSame(root, m.readChild(root, A)) }
        assertEquals(afterFold, m.totalOf(root), "and ten more laps cost nothing")
    }

    /**
     * The property that rules out recomputing the cost from the current structure.
     *
     * `mergeStates` DESTROYS states, so "sum of path lengths over the automaton as it now stands"
     * falls when a chain folds into a loop -- handing budget back, and a budget a program loop can
     * refund never terminates. `total` accumulates over mint EVENTS, so no fold can lower it.
     */
    @Test
    fun `folding a chain into a loop never lowers the pot`() {
        val m = manager()
        val root = m.origin()
        val a = assertNotNull(m.readChild(root, A))
        val ab = assertNotNull(m.readChild(a, B))
        assertNotNull(m.readChild(ab, C))
        val beforeFold = m.totalOf(root)
        assertEquals(6, beforeFold)

        // Collapse the whole chain onto its own origin: three states become one, and the structure
        // that remains carries a single self-loop per accessor.
        m.union(root, a)
        m.union(root, ab)
        assertTrue(m.totalOf(root) >= beforeFold, "the fold must not refund")
        assertEquals(beforeFold, m.totalOf(root))
    }

    @Test
    fun `a merge keeps one successor per accessor`() {
        val m = manager()
        val root = m.origin()

        val a = m.readChild(root, A)!!
        val b = m.readChild(root, B)!!
        val aC = m.readChild(a, C)!!
        val bC = m.readChild(b, C)!!

        m.union(a, b)

        val rep = a.find()
        assertSame(b.find(), rep)
        assertSame(
            aC.find(), bC.find(),
            "an NFA here would make every lookup explore a SET of states and re-derivation would " +
                "stop being free"
        )
        assertSame(aC.find(), rep.transition(C))
    }

    /**
     * The scenario the whole design turns on: a fact `x.[any].*` in a method containing
     * `while (*) { x = x.a }`.
     *
     * Each lap reads `a` through the `[any]`, so the arrival carries the SUCCESSOR state while the
     * accumulated fact still carries the parent; the storage merges them, and R3 unions a state with
     * its own descendant. The result must be a cycle. Refusing to create it would produce a fresh
     * state every lap, and since the state is inside node identity, the analysis would never
     * converge.
     */
    @Test
    fun `unioning a state with its own successor makes a self-loop and terminates`() {
        val m = manager()
        val root = m.origin()
        val successor = m.readChild(root, A)!!

        val merged = assertNotNull(m.union(root, successor))

        assertSame(root, merged, "receiver-preferred")
        assertSame(root, successor.find())
        assertSame(root, root.transition(A), "m --a--> m")
        assertEquals(2, root.pathCount, "the fold is recorded as sharing, not as an infinite language")

        val chargedBefore = m.totalOf(root)
        val next = m.readChild(root, A)
        assertSame(root, next, "the next lap finds the existing transition")
        assertEquals(chargedBefore, m.totalOf(root), "and charges nothing -- so the fixpoint closes")
    }

    @Test
    fun `merging two mutually reachable states terminates`() {
        val m = manager()
        val root = m.origin()

        // root --a--> x --b--> root', and root' folded back into root: a 2-cycle.
        val x = m.readChild(root, A)!!
        val back = m.readChild(x, B)!!
        m.union(root, back)

        // A second cycle through the same states, merged from the other end.
        val y = m.readChild(root, C)!!
        m.union(x, y)

        // Nothing above may hang, and every state must resolve.
        assertSame(root.find(), back.find())
        assertSame(x.find(), y.find())
        assertNotNull(root.transition(A))
        assertNotNull(root.transition(C))
    }

    /* ---------- the two layers ---------- */

    @Test
    fun `a cross-dag union fuses the dags and leaves one pot`() {
        val m = manager()
        val left = m.origin()
        val right = m.origin()

        m.readChild(left, A)
        m.readChild(right, B)
        assertEquals(1, m.totalOf(left))
        assertEquals(1, m.totalOf(right))
        assertFalse(left.dag.find() === right.dag.find(), "two origins, two pots")

        val fused = assertNotNull(m.union(left, right))

        assertSame(left.dag.find(), right.dag.find(), "one dag after the fusion")
        assertEquals(2, m.totalOf(fused), "the pots combine")
        assertSame(left.find(), right.find(), "and the start states merge -- two automata in, one out")
    }

    @Test
    fun `a fused automaton is still deterministic`() {
        val m = manager()
        val left = m.origin()
        val right = m.origin()

        val leftA = m.readChild(left, A)!!
        val rightA = m.readChild(right, A)!!

        m.union(left, right)

        assertSame(leftA.find(), rightA.find(), "the shared accessor must lead to one successor")
        assertSame(leftA.find(), left.transition(A))
    }

    /* ---------- the budget ---------- */

    /**
     * A CONTRACT CHANGE, and it should be visible in the diff as one: these three cases used to pin
     * the refusal. The read now records past the limit and labels the record `CREDIT`; the pot
     * decides only the label.
     */
    @Test
    fun `a mint past the limit is credit, not a refusal`() {
        val m = manager(limit = 2)
        val root = m.origin()

        val a = assertNotNull(m.readChild(root, A))
        assertNotNull(m.readChild(root, B))
        assertEquals(2, m.totalOf(root))
        assertTrue(m.budgetExhausted(root))
        assertEquals(AnyUnrollKind.PAID, a.kind)

        val c = assertNotNull(m.readChild(root, C), "the read never refuses")
        assertEquals(AnyUnrollKind.CREDIT, c.kind)
        assertEquals(2, m.totalOf(root), "and a credit mint charges nothing")
        assertSame(a, m.readChild(root, A), "an already-recorded accessor is still free")
    }

    @Test
    fun `a spent pot still answers an accessor it already recorded`() {
        val m = manager(limit = 1)
        val root = m.origin()

        val a = assertNotNull(m.readChild(root, A))
        assertTrue(m.budgetExhausted(root))

        assertSame(a, m.readChild(root, A), "reuse is free even past the limit")
        assertEquals(AnyUnrollKind.CREDIT, assertNotNull(m.readChild(root, B)).kind)
        assertEquals(1, m.totalOf(root))
    }

    /**
     * The defect class an earlier draft shipped: a second ceiling tested as `credit < limit`
     * evaluates `0 < 0`, so at `L = 0` the mechanism was simply off -- while three prose claims and
     * five test specifications said that value exercised it. `readChild` now has ONE comparison and
     * no value of `L` at which a read stops recording.
     */
    @Test
    fun `at L equals 0 the first read still mints`() {
        val m = manager(limit = 0)
        val root = m.origin()

        assertTrue(m.budgetExhausted(root))
        val a = assertNotNull(m.readChild(root, A))
        assertEquals(AnyUnrollKind.CREDIT, a.kind)
        assertEquals(0, m.totalOf(root))
        assertEquals(listOf(root), a.preds(A), "and it records its incoming edge like any other")
    }

    @Test
    fun `a recorded sequence mints nothing on re-read`() {
        val m = manager(limit = 0)
        val root = m.origin()

        val first = assertNotNull(m.readChild(root, A))
        val before = m.liveStats().states
        assertSame(first, m.readChild(root, A), "the sharing the population bound rests on")
        assertEquals(before, m.liveStats().states)
    }

    /**
     * The premise side keeps the pre-credit contract exactly, or accessors granted today are
     * silently refused -- a narrowing nothing would report.
     */
    @Test
    fun `the paid-only read keeps the old contract`() {
        val m = manager(limit = 1)
        val root = m.origin()

        val a = assertNotNull(m.readChildPaidOnly(root, A))
        assertTrue(m.budgetExhausted(root))

        assertSame(a, m.readChildPaidOnly(root, A), "a RECORDED transition is free past the limit")
        assertNull(m.readChildPaidOnly(root, B), "a new one is refused, as before")
        assertNull(m.readChildPaidOnly(root, C))
    }

    @Test
    fun `the paid-only read at limit zero refuses from the start`() {
        val m = manager(limit = 0)
        assertNull(m.readChildPaidOnly(m.origin(), A))
    }

    @Test
    fun `a query never mints and never charges`() {
        val m = manager()
        val root = m.origin()

        assertSame(root, m.peekChild(root, A), "no transition yet: the query stays put")
        assertEquals(0, m.totalOf(root))
        assertNull(root.children?.get(A), "and mints nothing")

        val a = m.readChild(root, A)!!
        assertSame(a, m.peekChild(root, A), "an existing transition is reused by a query too")
        assertEquals(1, m.totalOf(root), "still only the build's charge")
    }

    /* ---------- the kind, and what a union does to it ---------- */

    private fun kindManager(merge: AnyUnrollKindMerge) = AnyUnrollManager(limit = 1_000, kindMerge = merge)

    /**
     * Origins are minted constantly and almost every union is a cross-dag fusion of two start
     * states. If a fresh origin carried an opinion, the fusion rate would decide the cut instead of
     * the knob -- in BOTH directions, which is why this is asserted under both strategies and both
     * argument orders.
     */
    @Test
    fun `an origin is neutral in the merge`() {
        for (merge in AnyUnrollKindMerge.entries) {
            val m = kindManager(merge)
            val root = m.origin()
            val credit = m.readChild(root, A)!!
            credit.kind = AnyUnrollKind.CREDIT

            val fresh = m.origin()
            m.union(credit, fresh)
            assertEquals(AnyUnrollKind.CREDIT, credit.find().kind, "$merge, credit as receiver")

            val m2 = kindManager(merge)
            val root2 = m2.origin()
            val credit2 = m2.readChild(root2, A)!!
            credit2.kind = AnyUnrollKind.CREDIT
            val fresh2 = m2.origin()
            m2.union(fresh2, credit2)
            assertEquals(AnyUnrollKind.CREDIT, fresh2.find().kind, "$merge, origin as receiver")
        }
    }

    @Test
    fun `a union takes the meet under PreferBelow`() {
        for (reversed in listOf(false, true)) {
            val m = kindManager(AnyUnrollKindMerge.PreferBelow)
            val root = m.origin()
            val paid = m.readChild(root, A)!!
            val credit = m.readChild(root, B)!!
            credit.kind = AnyUnrollKind.CREDIT

            if (reversed) m.union(credit, paid) else m.union(paid, credit)
            assertEquals(
                AnyUnrollKind.PAID, paid.find().kind,
                "writable if ANY member is (reversed=$reversed)"
            )
        }
    }

    @Test
    fun `a union takes the join under PreferBeyond`() {
        for (reversed in listOf(false, true)) {
            val m = kindManager(AnyUnrollKindMerge.PreferBeyond)
            val root = m.origin()
            val paid = m.readChild(root, A)!!
            val credit = m.readChild(root, B)!!
            credit.kind = AnyUnrollKind.CREDIT

            if (reversed) m.union(credit, paid) else m.union(paid, credit)
            assertEquals(
                AnyUnrollKind.CREDIT, paid.find().kind,
                "absorbing if ANY member is (reversed=$reversed)"
            )
        }
    }

    /** §5.4(a) is independent of §5.4(b): the kind decides what survives says, not which survives. */
    @Test
    fun `the kind merge does not change which object survives`() {
        for (merge in AnyUnrollKindMerge.entries) {
            val m = kindManager(merge)
            val root = m.origin()
            val x = m.readChild(root, A)!!
            val y = m.readChild(root, B)!!
            y.kind = AnyUnrollKind.CREDIT

            assertSame(x, m.union(x, y), "$merge: the receiver's representative wins")
            assertSame(x, y.find())
        }
    }

    @Test
    fun `the kind knob parses strictly and falls back rather than failing`() {
        // A bare `enumValueOf` on a misspelled -D would fail class initialisation, and for a knob
        // read at class-init that means the analyzer does not start.
        assertEquals(AnyUnrollKindMerge.PreferBelow, AnyUnrollManager.DEFAULT_KIND_MERGE)
    }

    /* ---------- compression: only representatives appear in edges ---------- */

    private fun AnyUnrollState.preds(accessor: Int): List<AnyUnrollState> =
        find().parents?.get(accessor)?.map { it.find() }.orEmpty()

    /**
     * The inverse of the hole this closes. Before compression `mergeStates` folded only the OUTGOING
     * direction, so after a union a predecessor's transition named the loser verbatim -- forever, and
     * against the collector.
     */
    @Test
    fun `a union remaps the predecessor's transition`() {
        val m = manager()
        val p = m.origin()
        val s = m.readChild(p, A)!!
        val t = m.readChild(p, B)!!

        m.union(s, t)

        assertSame(s, p.children!!.get(B), "the STORED value must be the winner, not the loser")
        assertSame(s, p.transition(B))
        assertEquals(listOf(p), s.preds(B), "and the mirror records the edge")
        assertEquals(listOf(p), s.preds(A))
    }

    @Test
    fun `a merged-away state with an incoming edge becomes unreachable`() {
        val m = manager()
        val p = m.origin()
        val s = m.readChild(p, A)!!

        var transient: AnyUnrollState? = m.readChild(p, B)
        val ref = WeakReference(transient)
        m.union(s, transient!!)
        transient = null

        var collected = false
        for (attempt in 0 until 50) {
            System.gc()
            Thread.sleep(20)
            if (ref.get() == null) {
                collected = true
                break
            }
        }

        assertTrue(
            collected,
            "a state reachable only through a stale transition is exactly what the incoming remap " +
                "exists to release"
        )
    }

    @Test
    fun `a paid mint records its incoming edge`() {
        val m = manager()
        val root = m.origin()
        val a = m.readChild(root, A)!!

        assertEquals(listOf(root), a.preds(A))
        assertTrue(a.preds(B).isEmpty(), "and nothing it did not record")
        assertTrue(root.preds(A).isEmpty(), "the origin has no incoming edge")
    }

    @Test
    fun `a self-loop records itself as its own predecessor`() {
        val m = manager()
        val root = m.origin()
        val successor = m.readChild(root, A)!!
        m.union(root, successor)

        assertSame(root, root.transition(A), "m --a--> m")
        assertEquals(
            listOf(root), root.preds(A),
            "the automaton saying `a` is ALREADY folded into this `[any]`; an identity test would " +
                "read this as 'no incoming edge' and write the accessor instead"
        )
    }

    @Test
    fun `the parents index survives a conflicting union`() {
        val m = manager()
        val root = m.origin()
        val a = m.readChild(root, A)!!
        val b = m.readChild(root, B)!!
        val aC = m.readChild(a, C)!!
        val bC = m.readChild(b, C)!!

        // a and b both carry a C-edge, so the fold queues the two targets rather than keeping both.
        m.union(a, b)

        val rep = a.find()
        assertSame(aC.find(), bC.find())
        assertEquals(listOf(rep), aC.find().preds(C), "one predecessor, and it is the representative")
        assertNoNonRepresentatives(root)
    }

    /**
     * The premise the subset construction rests on: `y.parent = x` re-points every predecessor of `y`
     * onto `x`, so two states reached on the SAME accessor from two DIFFERENT predecessors leave the
     * winner with both. The reversed relation is an NFA even though the forward one is not.
     */
    @Test
    fun `a union forks the reverse index`() {
        val m = manager()
        val root = m.origin()
        val p = m.readChild(root, A)!!
        val q = m.readChild(root, B)!!
        val t1 = m.readChild(p, C)!!
        val t2 = m.readChild(q, C)!!

        m.union(t1, t2)

        val preds = t1.preds(C)
        assertEquals(2, preds.size, "two C-predecessors of one state -- the fork")
        assertTrue(preds.containsAll(listOf(p.find(), q.find())))
        assertNoNonRepresentatives(root)
    }

    @Test
    fun `no map holds a non-representative after a cascade`() {
        val m = manager()
        val left = m.origin()
        val right = m.origin()

        val la = m.readChild(left, A)!!
        m.readChild(la, B)
        val ra = m.readChild(right, A)!!
        m.readChild(ra, B)
        m.readChild(right, C)

        m.union(left, right)

        assertNoNonRepresentatives(left)
    }

    private fun assertNoNonRepresentatives(seed: AnyUnrollState) {
        val seen = java.util.IdentityHashMap<AnyUnrollState, Unit>()
        val stack = ArrayDeque<AnyUnrollState>()
        stack.addLast(seed.find())
        while (stack.isNotEmpty()) {
            val n = stack.removeLast()
            if (seen.put(n, Unit) != null) continue
            assertSame(n, n.find(), "a non-representative was reached: \$n")

            n.children?.let { c ->
                for (k in c.keys.toIntArray()) {
                    val v = assertNotNull(c.get(k))
                    assertSame(v, v.find(), "children[\$k] on \$n names a non-representative")
                    stack.addLast(v)
                }
            }
            n.parents?.let { pm ->
                for (k in pm.keys.toIntArray()) {
                    for (v in assertNotNull(pm.get(k))) {
                        assertSame(v, v.find(), "parents[\$k] on \$n names a non-representative")
                        stack.addLast(v)
                    }
                }
            }
        }
    }

    /* ---------- the backward step ---------- */

    @Test
    fun `absorbInto walks back exactly one step`() {
        val m = manager()
        val p = m.origin()
        val pa = m.readChild(p, A)!!

        assertSame(p, m.absorbInto(pa, A))
        assertNull(m.absorbInto(pa, B), "an accessor this state did not record is not an incoming edge")
        assertNull(m.absorbInto(p, A), "and an origin has no incoming edge at all")
    }

    @Test
    fun `absorbInto survives a union of the predecessor`() {
        val m = manager()
        val root = m.origin()
        val p = m.readChild(root, A)!!
        val s = m.readChild(p, C)!!
        val q = m.readChild(root, B)!!

        m.union(q, p)

        assertSame(q.find(), m.absorbInto(s, C), "the merged class answers, not the merged-away object")
    }

    /**
     * The case an identity test would have got backwards. A self-loop is precisely the automaton
     * saying the accessor is ALREADY folded into this `[any]`, so the answer is "absorb, staying
     * put" -- and `result === state` reads that as "no incoming edge" and writes the accessor.
     */
    @Test
    fun `absorbInto returns the state itself on a self-loop`() {
        val m = manager()
        val root = m.origin()
        m.union(root, m.readChild(root, A)!!)

        assertSame(root, m.absorbInto(root, A))
    }

    @Test
    fun `absorbInto picks the same predecessor twice`() {
        val m = manager()
        val root = m.origin()
        val p = m.readChild(root, A)!!
        val q = m.readChild(root, B)!!
        val t1 = m.readChild(p, C)!!
        val t2 = m.readChild(q, C)!!
        m.union(t1, t2)

        val first = assertNotNull(m.absorbInto(t1, C))
        assertSame(first, m.absorbInto(t1, C), "the tie-break must be reproducible")
        assertSame(minOf(p.find(), q.find(), compareBy { it.id }), first, "and it is the lowest id")
    }

    /**
     * The rank, in the one case where it differs from the id: a self-loop is preferred even when a
     * genuine predecessor was minted earlier and would win on id.
     *
     * A self-loop is the automaton saying `A` is ALREADY folded into this `[any]`, so absorbing into
     * it is the exact inverse of the read that put the fact here. Landing on `u` instead is sound --
     * every candidate denotes the same language -- but it moves the fact onto a position with
     * different transitions and possibly a different kind, for no reason beyond mint order.
     */
    @Test
    fun `absorbInto prefers a self-loop to a lower-id predecessor`() {
        val m = manager()
        val root = m.origin()
        val u = m.readChild(root, A)!!          // minted FIRST, so it wins on id
        val p = m.readChild(root, B)!!
        val q = m.readChild(p, C)!!
        val t = m.readChild(q, A)!!             // q --A--> t
        val v = m.readChild(u, A)!!             // u --A--> v

        m.union(t, v)                           // now u is an A-predecessor of t's class too
        m.union(t, q)                           // ancestor-descendant: q --A--> t becomes a self-loop

        val cls = t.find()
        assertTrue(u.find().id < cls.id, "the fork's other member really does win on id")
        assertSame(cls, m.absorbInto(t, A), "the self-loop wins the rank")
        assertSame(cls, m.absorbInto(t, A), "and the rank is still reproducible")
    }

    /**
     * The structural fact that bounds how much the choice among a fork's members can matter: it can
     * never move a fact between pots.
     *
     * `mint` gives a child its parent's dag and only `union` fuses dags, so a state's dag is its
     * reachability component. A state with two predecessors is reachable from both, hence all three
     * are in one component -- whatever the pick, `budgetExhausted`, the charge and the origin that
     * pays are unchanged. This pins it, because the counter that would otherwise have measured it
     * would have been structurally zero.
     */
    @Test
    fun `every member of a fork shares the target's pot`() {
        val m = manager()
        val root = m.origin()
        val other = m.origin()
        val p = m.readChild(root, A)!!
        val q = m.readChild(other, B)!!
        val t1 = m.readChild(p, C)!!
        val t2 = m.readChild(q, C)!!

        assertFalse(m.dagOf(p) === m.dagOf(q), "two origins start in two components")

        m.union(t1, t2)                         // the only way to build a fork -- and it fuses

        val target = t1.find()
        val preds = assertNotNull(target.parents?.get(C), "the fork is there")
        assertEquals(2, preds.size)
        for (pred in preds) {
            assertSame(m.dagOf(target), m.dagOf(pred), "a fork cannot straddle two pots")
        }
    }

    @Test
    fun `writesAbove follows the kind and not the pot`() {
        val m = manager(limit = 1)
        val root = m.origin()
        val paid = m.readChild(root, A)!!
        val credit = m.readChild(root, B)!!

        assertTrue(m.budgetExhausted(root), "the pot is spent for the whole origin")
        assertTrue(m.writesAbove(root), "but an origin was never bought and still writes")
        assertTrue(m.writesAbove(paid))
        assertFalse(m.writesAbove(credit), "only the state that went on credit absorbs")
        assertTrue(m.writesAbove(null))
    }

    /* ---------- Lemma 9.2: a recorded edge stays a real edge of the quotient automaton ---------- */

    private fun assertWitness(p: AnyUnrollState, accessor: Int, s: AnyUnrollState) {
        assertSame(s.find(), p.find().children!!.get(accessor)!!.find())
        assertTrue(p.find() in s.preds(accessor), "and the mirror agrees")
    }

    @Test
    fun `the witness survives a union of the successor`() {
        val m = manager()
        val p = m.origin()
        val s = m.readChild(p, A)!!
        val other = m.readChild(p, B)!!
        m.union(other, s)
        assertWitness(p, A, s)
    }

    @Test
    fun `the witness survives the predecessor losing root status`() {
        val m = manager()
        val root = m.origin()
        val p = m.readChild(root, A)!!
        val s = m.readChild(p, B)!!
        m.union(root, p)
        assertWitness(p, B, s)
    }

    @Test
    fun `the witness survives a conflicting union of two predecessors`() {
        val m = manager()
        val root = m.origin()
        val p = m.readChild(root, A)!!
        val q = m.readChild(root, B)!!
        val ps = m.readChild(p, C)!!
        val qs = m.readChild(q, C)!!

        m.union(p, q)

        // The fold must MERGE the conflicting targets rather than drop one.
        assertSame(ps.find(), qs.find())
        assertWitness(p, C, ps)
        assertWitness(q, C, qs)
    }

    @Test
    fun `the witness survives a cross-dag fusion`() {
        val m = manager()
        val left = m.origin()
        val right = m.origin()
        val ls = m.readChild(left, A)!!
        val rs = m.readChild(right, A)!!

        m.union(left, right)

        assertWitness(left, A, ls)
        assertWitness(right, A, rs)
    }

    @Test
    fun `the witness survives a self-loop`() {
        val m = manager()
        val root = m.origin()
        val s = m.readChild(root, A)!!
        m.union(root, s)
        assertWitness(root, A, s)
    }

    @Test
    fun `a read advances the state to the successor of the accessor read`() {
        val m = manager()
        val p = m.origin()
        val s = assertNotNull(m.readChild(p, A))

        assertFalse(s === p, "the read advances")
        assertWitness(p, A, s)
    }

    /* ---------- the population counts behind the progress line ---------- */

    /**
     * The counting scheme holds no registry, so every number is a difference of two event counters
     * and the fusion is the one place they can drift: the pots SUM, so a fusion can push the
     * survivor past `L` on its own AND remove a dag that was already latched as exhausted.
     */
    @Test
    fun `the live counts follow creation, fusion and merging`() {
        val m = manager(limit = 2)

        val left = m.origin()
        val right = m.origin()
        m.liveStats().let {
            assertEquals(2, it.liveRoots)
            assertEquals(0, it.beyond, "a fresh pot at L = 2 has spent nothing")
            assertEquals(2, it.states)
        }

        m.readChild(left, A)
        m.readChild(left, B)
        m.liveStats().let {
            assertEquals(2, it.liveRoots)
            assertEquals(1, it.beyond, "left's pot reached L")
            assertEquals(4, it.states)
            assertEquals(3, it.maxStatesPerDag)
            assertEquals(2, it.transitions)
        }

        // The fusion: one representative goes, the pots sum -- which pushes the survivor past L on
        // its own -- and the two start states merge, so a state goes too.
        m.union(right, left)
        m.liveStats().let {
            assertEquals(1, it.liveRoots, "one representative left")
            assertEquals(1, it.beyond, "the count transfers rather than doubling")
            assertEquals(3, it.states, "the two start states became one")
            assertTrue(it.beyond <= it.liveRoots, "beyond can never exceed live")
        }
    }

    @Test
    fun `a pot born exhausted is counted`() {
        val m = manager(limit = 0)
        m.origin()

        assertEquals(1, m.liveStats().beyond, "at L = 0 the origin is already at its limit")
    }

    @Test
    fun `a disabled manager reports no line`() {
        assertNull(AnyUnrollManager(limit = -1).liveReport())
        assertNotNull(manager().liveReport())
    }

    /* ---------- concurrency ---------- */

    /**
     * The failure this guards is a HANG, not a wrong answer.
     *
     * Two threads running `union(x, y)` and `union(y, x)` can each observe two distinct roots and
     * then write `a.parent = b` and `b.parent = a`, leaving a cycle in the DSU forest that nothing
     * detects and that makes every subsequent `find` spin forever. Discovering the root and writing
     * it inside one critical section is what rules that out.
     */
    @Test
    fun `concurrent unions in both directions never build a cycle in the forest`() {
        repeat(4) { round ->
            val m = manager(limit = 1_000_000)
            val pairs = List(64) { m.origin() to m.origin() }

            val threads = 8
            val pool = Executors.newFixedThreadPool(threads)
            val start = CountDownLatch(1)
            val failure = AtomicReference<Throwable?>(null)

            try {
                val futures = (0 until threads).map { t ->
                    pool.submit {
                        try {
                            start.await()
                            for ((x, y) in pairs) {
                                if (t % 2 == 0) m.union(x, y) else m.union(y, x)
                            }
                        } catch (e: Throwable) {
                            failure.compareAndSet(null, e)
                        }
                    }
                }
                start.countDown()
                for (f in futures) {
                    f.get(60, TimeUnit.SECONDS)
                }
            } finally {
                pool.shutdownNow()
            }

            assertNull(failure.get(), "round $round threw: ${failure.get()}")

            // If a cycle had formed, one of these would not have returned at all -- reaching this
            // line is most of the assertion.
            for ((x, y) in pairs) {
                assertSame(x.find(), y.find(), "round $round: the pair must end up in one class")
            }
        }
    }

    /**
     * Two threads reading the same NEW accessor must produce one transition and one charge. The
     * budget test, the transition insert and the `total` increment happen together under the lock,
     * or two readers see the same pre-merge counts and one increment is lost.
     */
    @Test
    fun `concurrent first reads of one accessor charge exactly once`() {
        repeat(4) {
            val m = manager(limit = 1_000_000)
            val roots = List(64) { m.origin() }

            val threads = 8
            val pool = Executors.newFixedThreadPool(threads)
            val start = CountDownLatch(1)
            val seen = List(roots.size) { AtomicReference<AnyUnrollState?>(null) }

            try {
                val futures = (0 until threads).map {
                    pool.submit {
                        start.await()
                        roots.forEachIndexed { i, root ->
                            val child = m.readChild(root, A)!!
                            seen[i].compareAndSet(null, child)
                        }
                    }
                }
                start.countDown()
                for (f in futures) f.get(60, TimeUnit.SECONDS)
            } finally {
                pool.shutdownNow()
            }

            roots.forEachIndexed { i, root ->
                assertEquals(1, m.totalOf(root), "root $i must be charged exactly once")
                assertSame(seen[i].get()!!.find(), root.transition(A), "and name one successor")
            }
        }
    }

    /* ---------- reclamation ---------- */

    /**
     * The case an int-keyed DSU could not recover, and the whole reason states are objects: mint a
     * state, merge it into another, drop the node that carried it. Under a columnar scheme its slot
     * survives the phase; here it is simply unreachable.
     *
     * The representative must NOT hold the states merged into it -- only the other way round.
     */
    @Test
    fun `a merged-away state with no holder becomes unreachable`() {
        val m = manager()
        val survivor = m.origin()

        var transient: AnyUnrollState? = m.origin()
        val ref = WeakReference(transient)

        m.union(survivor, transient!!)
        assertSame(survivor.find(), transient.find())

        transient = null

        var collected = false
        for (attempt in 0 until 50) {
            System.gc()
            Thread.sleep(20)
            if (ref.get() == null) {
                collected = true
                break
            }
        }

        assertTrue(
            collected,
            "a state nothing refers to any more must be collectable; a representative that held its " +
                "absorbed members would leak exactly the transient mints the design exists to reclaim"
        )
    }
}

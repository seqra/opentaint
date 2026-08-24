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

    private fun manager(limit: Int = 1_000) = AnyUnrollManager(limit)

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

    @Test
    fun `the charge is the path count, not one`() {
        val m = manager()
        val root = m.origin()
        val a = m.readChild(root, A)!!
        val b = m.readChild(root, B)!!
        assertEquals(2, m.totalOf(root))

        val shared = assertNotNull(m.union(a, b))
        assertEquals(2, shared.pathCount)

        m.readChild(shared, C)
        assertEquals(
            4, m.totalOf(root),
            "emitting `c` at a state two sequences reach authorises `ac` and `bc`, so it costs 2"
        )
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

    @Test
    fun `the pot refuses once it is spent`() {
        val m = manager(limit = 2)
        val root = m.origin()

        val a = assertNotNull(m.readChild(root, A))
        assertNotNull(m.readChild(root, B))
        assertEquals(2, m.totalOf(root))
        assertTrue(m.budgetExhausted(root))

        assertNull(m.readChild(root, C), "a spent pot refuses a new accessor")
        assertSame(a, m.readChild(root, A), "but an already-recorded one is still free")
    }

    @Test
    fun `a spent pot still answers an accessor it already recorded`() {
        val m = manager(limit = 1)
        val root = m.origin()

        val a = assertNotNull(m.readChild(root, A))
        assertTrue(m.budgetExhausted(root))

        assertSame(a, m.readChild(root, A), "reuse is free even past the limit")
        assertNull(m.readChild(root, B), "a new accessor is not")
    }

    @Test
    fun `limit zero refuses from the start`() {
        val m = manager(limit = 0)
        val root = m.origin()

        assertTrue(m.budgetExhausted(root))
        assertNull(m.readChild(root, A))
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

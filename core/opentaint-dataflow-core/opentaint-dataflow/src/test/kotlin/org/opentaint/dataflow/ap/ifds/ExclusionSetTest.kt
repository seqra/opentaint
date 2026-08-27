package org.opentaint.dataflow.ap.ifds

import kotlinx.collections.immutable.persistentHashSetOf
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * The contract of [ExclusionSet], with the read/write split.
 *
 * Three groups matter beyond the obvious set behaviour:
 *
 * - **Flat preservation.** `read ∪ write` is what every consumer of an exclusion set actually reads, and
 *   both merges must compute exactly the accessor set the pre-split implementation computed. Every merge
 *   test asserts the flat result as well as the labels.
 * - **The `===` contract.** About a dozen storages use `merged === current` as their "nothing new"
 *   fixpoint signal. If a merge allocates when it did not have to, the engine stops converging — a
 *   failure mode that shows up as a hang, not as a wrong answer.
 * - **Hashing.** `ExclusionSet` is a hash-map key in every storage, and the incremental hash maintained
 *   by `addRead`/`addWrite` must agree with the from-scratch hash the merges compute.
 */
class ExclusionSetTest {
    private val a = FieldAccessor("A", "a", "T")
    private val b = FieldAccessor("A", "b", "T")
    private val c = FieldAccessor("A", "c", "T")

    private fun concrete(read: Set<Accessor> = emptySet(), write: Set<Accessor> = emptySet()) =
        ExclusionSet.Concrete.create(
            persistentHashSetOf<Accessor>().addAll(read).addAll(write),
            persistentHashSetOf<Accessor>().addAll(write)
        )

    private val ExclusionSet.flat: Set<Accessor>
        get() = (this as ExclusionSet.Concrete).flat

    private val ExclusionSet.writeSet: Set<Accessor>
        get() = (this as ExclusionSet.Concrete).write

    private val ExclusionSet.readSet: Set<Accessor>
        get() = (this as ExclusionSet.Concrete).read

    // --- queries ---------------------------------------------------------------------------------

    @Test
    fun `empty demands nothing`() {
        assertFalse(a in ExclusionSet.Empty)
        assertFalse(ExclusionSet.Empty.containsRead(a))
        assertFalse(ExclusionSet.Empty.containsWrite(a))
    }

    @Test
    fun `universe demands everything and is kind-neutral`() {
        assertTrue(a in ExclusionSet.Universe)
        // No abstract tail means no demand, so there is no kind to report.
        assertFalse(ExclusionSet.Universe.containsRead(a))
        assertFalse(ExclusionSet.Universe.containsWrite(a))
    }

    @Test
    fun `contains reads the flat set regardless of kind`() {
        val set = concrete(read = setOf(a), write = setOf(b))

        assertTrue(a in set)
        assertTrue(b in set)
        assertFalse(c in set)

        assertTrue(set.containsRead(a))
        assertFalse(set.containsWrite(a))
        assertFalse(set.containsRead(b))
        assertTrue(set.containsWrite(b))
    }

    // --- growth ----------------------------------------------------------------------------------

    @Test
    fun `growing an empty set produces a single demand of the requested kind`() {
        val read = ExclusionSet.Empty.addRead(a)
        assertEquals(setOf(a), read.flat)
        assertEquals(setOf(a), read.readSet)
        assertEquals(emptySet<Accessor>(), read.writeSet)

        val write = ExclusionSet.Empty.addWrite(a)
        assertEquals(setOf(a), write.flat)
        assertEquals(emptySet<Accessor>(), write.readSet)
        assertEquals(setOf(a), write.writeSet)
    }

    @Test
    fun `universe absorbs both kinds of growth`() {
        assertSame(ExclusionSet.Universe, ExclusionSet.Universe.addRead(a))
        assertSame(ExclusionSet.Universe, ExclusionSet.Universe.addWrite(a))
    }

    @Test
    fun `re-adding an outstanding demand of the same kind returns the receiver`() {
        val read = concrete(read = setOf(a))
        assertSame(read, read.addRead(a))

        val write = concrete(write = setOf(a))
        assertSame(write, write.addWrite(a))
    }

    @Test
    fun `a read demand does not demote an outstanding write demand`() {
        val write = concrete(write = setOf(a))
        assertSame(write, write.addRead(a))
    }

    @Test
    fun `a write demand promotes an outstanding read demand in place`() {
        val read = concrete(read = setOf(a, b))
        val promoted = read.addWrite(a)

        assertEquals(setOf(a, b), promoted.flat, "promotion must not change the flat set")
        assertEquals(setOf(a), promoted.writeSet)
        assertEquals(setOf(b), promoted.readSet)
    }

    @Test
    fun `add dispatches on the kind`() {
        assertEquals(ExclusionSet.Empty.addRead(a), ExclusionSet.Empty.add(a, ExclusionKind.READ))
        assertEquals(ExclusionSet.Empty.addWrite(a), ExclusionSet.Empty.add(a, ExclusionKind.WRITE))
    }

    // --- representation invariants ---------------------------------------------------------------

    @Test
    fun `read and write stay disjoint`() {
        val set = concrete(read = setOf(a, b), write = setOf(c)).addWrite(a)
        assertEquals(emptySet<Accessor>(), set.readSet intersect set.writeSet)
        assertEquals(set.flat, set.readSet + set.writeSet)
    }

    @Test
    fun `the factory clamps write to flat and normalises the empty demand`() {
        // A write label for an accessor that is not in the demand at all has nothing to label.
        val clamped = ExclusionSet.Concrete.create(persistentHashSetOf(a), persistentHashSetOf(a, b))
        assertEquals(setOf(a), clamped.flat)
        assertEquals(setOf(a), clamped.writeSet)

        assertSame(
            ExclusionSet.Empty,
            ExclusionSet.Concrete.create(persistentHashSetOf(), persistentHashSetOf())
        )
    }

    // --- hashing and equality --------------------------------------------------------------------

    @Test
    fun `the same accessor under different kinds is a different value`() {
        val read = concrete(read = setOf(a))
        val write = concrete(write = setOf(a))

        assertNotEquals(read, write)
        assertNotEquals(
            read.hashCode(), write.hashCode(),
            "read and write demands on the same accessor must not collide as hash-map keys"
        )
    }

    @Test
    fun `swapping which accessor carries the write label is a different value`() {
        val first = concrete(read = setOf(a), write = setOf(b))
        val second = concrete(read = setOf(b), write = setOf(a))

        assertNotEquals(first, second)
        assertNotEquals(first.hashCode(), second.hashCode())
    }

    @Test
    fun `the incremental hash agrees with the from-scratch hash`() {
        val grown = ExclusionSet.Empty.addRead(a).addWrite(b).addRead(c).addWrite(a)
        val built = concrete(read = setOf(c), write = setOf(a, b))

        assertEquals(built, grown)
        assertEquals(built.hashCode(), grown.hashCode())

        // The merges recompute the hash from scratch; it must land on the same value.
        val merged = concrete(read = setOf(a, c)).union(concrete(write = setOf(a, b)))
        assertEquals(built, merged)
        assertEquals(built.hashCode(), merged.hashCode())
    }

    // --- union -----------------------------------------------------------------------------------

    @Test
    fun `union unions the flat sets and promotes shared accessors`() {
        val left = concrete(read = setOf(a, b))
        val right = concrete(read = setOf(c), write = setOf(a))

        val merged = left.union(right)

        assertEquals(setOf(a, b, c), merged.flat)
        assertEquals(setOf(a), merged.writeSet)
        assertEquals(setOf(b, c), merged.readSet)
    }

    @Test
    fun `union has empty as its identity and universe as its zero`() {
        val set = concrete(read = setOf(a), write = setOf(b))

        assertSame(set, set.union(ExclusionSet.Empty))
        assertSame(set, ExclusionSet.Empty.union(set))

        assertSame(ExclusionSet.Universe, set.union(ExclusionSet.Universe))
        assertSame(ExclusionSet.Universe, ExclusionSet.Universe.union(set))
    }

    @Test
    fun `union is commutative, associative and idempotent`() {
        val x = concrete(read = setOf(a, b))
        val y = concrete(read = setOf(b), write = setOf(c))
        val z = concrete(write = setOf(a))

        assertEquals(x.union(y), y.union(x))
        assertEquals(x.union(y).union(z), x.union(y.union(z)))
        assertEquals(x, x.union(x))
    }

    @Test
    fun `union returns the receiver when the other demand is already subsumed`() {
        val set = concrete(read = setOf(a, b), write = setOf(c))

        assertSame(set, set.union(set))
        assertSame(set, set.union(concrete(read = setOf(a))))
        assertSame(set, set.union(concrete(write = setOf(c))))
        // A read demand on an accessor already carrying a write demand adds nothing.
        assertSame(set, set.union(concrete(read = setOf(c))))
    }

    @Test
    fun `union allocates when only the kind changes`() {
        // The one cost of the split: a promotion is a change even though the flat set — and therefore
        // every fact the engine derives from it — is untouched. Storages using `merged === current` as
        // their fixpoint signal see one extra change per accessor per slot, since `write` only grows.
        val set = concrete(read = setOf(a))
        val promoted = set.union(concrete(write = setOf(a)))

        assertEquals(set.flat, promoted.flat)
        assertNotEquals<ExclusionSet>(set, promoted)
    }

    // --- intersect -------------------------------------------------------------------------------

    @Test
    fun `intersect intersects the flat sets and promotes survivors`() {
        val left = concrete(read = setOf(a, b), write = setOf(c))
        val right = concrete(read = setOf(c), write = setOf(a))

        val merged = left.intersect(right)

        assertEquals(setOf(a, c), merged.flat)
        assertEquals(setOf(a, c), merged.writeSet, "a write label on either side survives the meet")
        assertEquals(emptySet<Accessor>(), merged.readSet)
    }

    @Test
    fun `intersect drops write labels whose accessor did not survive`() {
        val left = concrete(write = setOf(a, b))
        val right = concrete(read = setOf(b))

        val merged = left.intersect(right)

        assertEquals(setOf(b), merged.flat)
        assertEquals(setOf(b), merged.writeSet)
    }

    @Test
    fun `intersect has universe as its identity and empty as its zero`() {
        val set = concrete(read = setOf(a), write = setOf(b))

        assertSame(set, set.intersect(ExclusionSet.Universe))
        assertSame(set, ExclusionSet.Universe.intersect(set))

        assertSame(ExclusionSet.Empty, set.intersect(ExclusionSet.Empty))
        assertSame(ExclusionSet.Empty, ExclusionSet.Empty.intersect(set))
    }

    @Test
    fun `intersecting disjoint demands leaves nothing to refine`() {
        assertSame(ExclusionSet.Empty, concrete(read = setOf(a)).intersect(concrete(write = setOf(b))))
    }

    @Test
    fun `intersect is commutative, associative and idempotent`() {
        val x = concrete(read = setOf(a, b), write = setOf(c))
        val y = concrete(read = setOf(b, c), write = setOf(a))
        val z = concrete(read = setOf(a, c), write = setOf(b))

        assertEquals(x.intersect(y), y.intersect(x))
        assertEquals(x.intersect(y).intersect(z), x.intersect(y.intersect(z)))
        assertEquals(x, x.intersect(x))
    }

    @Test
    fun `intersect returns the receiver when the receiver is already the smaller demand`() {
        val set = concrete(read = setOf(a), write = setOf(b))

        assertSame(set, set.intersect(set))
        assertSame(set, set.intersect(concrete(read = setOf(a, c), write = setOf(b))))
    }

    @Test
    fun `intersect returns the receiver when the other write label does not survive`() {
        // Regression: computing (w1 ∪ w2) ∩ flat adds `c` and then removes it again, and
        // PersistentHashSet does not canonicalise that round trip back to the receiver. The result
        // is `equals` to the receiver but not `===`, so every storage keyed on the `===` fixpoint
        // signal reports a change forever. Clamp each side to the surviving flat set first.
        val set = concrete(read = setOf(a), write = setOf(b))
        assertSame(set, set.intersect(concrete(read = setOf(a, b, c), write = setOf(c))))

        val readOnly = concrete(read = setOf(a))
        assertSame(readOnly, readOnly.intersect(concrete(read = setOf(a), write = setOf(b))))
    }

    // --- flat preservation, stated directly ------------------------------------------------------

    @Test
    fun `both merges compute the pre-split accessor set`() {
        val left = concrete(read = setOf(a, b), write = setOf(c))
        val right = concrete(read = setOf(c), write = setOf(a))

        assertEquals(left.flat + right.flat, left.union(right).flat)
        assertEquals(left.flat intersect right.flat, left.intersect(right).flat)
    }
}

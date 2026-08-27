package org.opentaint.dataflow.ap.ifds

import kotlinx.collections.immutable.PersistentSet
import kotlinx.collections.immutable.persistentHashSetOf

/**
 * Why an accessor was added to an [ExclusionSet].
 *
 * The kinds form a two-element lattice `READ ⊑ WRITE`, read as demand strength: a point that must be
 * refined before a store must also be refined before a load, so [WRITE] subsumes [READ] at the same
 * accessor. Both merges of [ExclusionSet] take the join in this lattice, i.e. they promote.
 *
 * Nothing consumes the kind yet — see the class KDoc of [ExclusionSet].
 */
enum class ExclusionKind {
    /** The demand arose from reading through the accessor. */
    READ,

    /** The demand arose from writing through the accessor. */
    WRITE,
}

/**
 * Annotates the implicit star tail of an *abstract* access path: **this abstraction point has no
 * information about these accessors, and must be refined before anything can be concluded about them.**
 *
 * It is a refinement *demand*, not an assertion that the excluded branch is empty. The demand is
 * discharged by spawning a separate, more refined initial fact for the excluded branch
 * (`TreeInitialFactAbstraction.registerNewInitialFact`, `CactusInitialFactAbstraction`), which is what
 * makes *adding* to an exclusion set always safe: the coverage given up is picked up by the spawned
 * sibling.
 *
 * The denotation is flat and depth-1 — it constrains immediate children only:
 * ```
 * γ(a.* \ E) = { a } ∪ { a.f.p │ f ∉ E }
 * ```
 * so `x.*\{f}` does **not** exclude `x.g.f`. All four `filter` implementations
 * (`AccessTree`, `AccessCactus`, `AccessPath`, `AccessGraph`) transform only the top level.
 *
 * | Value | Meaning |
 * | --- | --- |
 * | [Empty] | Maximally abstract — nothing demands refinement. |
 * | [Concrete] | Abstract, with a refinement demand outstanding on every accessor in the set. |
 * | [Universe] | No abstract tail at all — the fact is exact, so there is nothing to refine. |
 *
 * ### Read/write split
 *
 * [Concrete] partitions its accessors into two disjoint sets by [ExclusionKind]. The union of the two —
 * [Concrete.flat] — is the whole demand, and it is the *only* thing any current consumer looks at:
 * [contains], the four `filter` implementations, both flow-function guards
 * (`mayReadAccessor` / `mayRemoveAfterWrite`) and the abstraction registries all read `flat`.
 *
 * Both merges preserve `flat` exactly:
 * ```
 * union:      flat = flat₁ ∪ flat₂ ,  write = w₁ ∪ w₂
 * intersect:  flat = flat₁ ∩ flat₂ ,  write = (w₁ ∪ w₂) ∩ flat
 * ```
 * so the split is a *labelling* change: every fact the engine derives is the fact it derived before
 * the split, and each demand now additionally records whether it arose from a read or from a write.
 *
 * It is not free, though. Exclusions are part of fact identity, and the label is part of exclusion
 * identity, so `a.*\{f:READ}` and `a.*\{f:WRITE}` are two keys where they used to be one — until a
 * merge promotes them back together. That costs extra edges and extra fixpoint iterations, bounded by
 * the fact that `write` only ever grows within a fixed `flat`. It costs no findings.
 *
 * The guards must keep querying `flat` — the flow functions gate re-emission on
 * `accessor !in exclusions`, so a guard that queried one half while the producer wrote the other would
 * never see its accessor and would re-emit forever.
 *
 * Design doc: `docs/design/exclusion-set-read-write-split.md`.
 */
sealed interface ExclusionSet {
    operator fun contains(accessor: Accessor): Boolean

    /**
     * `true` if an outstanding refinement demand on [accessor] arose from a read.
     *
     * This reports a *demand*, not exclusion: [Universe] excludes every accessor yet answers `false`
     * here, because a fact with no abstract tail has nothing left to refine. Ask [contains] to learn
     * whether an accessor is excluded; ask this only about the provenance of a demand you already know
     * exists.
     */
    fun containsRead(accessor: Accessor): Boolean

    /** `true` if an outstanding refinement demand on [accessor] arose from a write. See [containsRead]. */
    fun containsWrite(accessor: Accessor): Boolean

    fun addRead(accessor: Accessor): ExclusionSet
    fun addWrite(accessor: Accessor): ExclusionSet

    fun add(accessor: Accessor, kind: ExclusionKind): ExclusionSet = when (kind) {
        ExclusionKind.READ -> addRead(accessor)
        ExclusionKind.WRITE -> addWrite(accessor)
    }

    /**
     * Merges two demands: the accessor sets are unioned and the kind of a shared accessor is promoted
     * to the stronger of the two. Identity is [Empty].
     */
    fun union(other: ExclusionSet): ExclusionSet

    /**
     * Subsumes two demands: the accessor sets are intersected and the kind of a surviving accessor is
     * promoted to the stronger of the two. Identity is [Universe].
     */
    fun intersect(other: ExclusionSet): ExclusionSet

    data object Empty : ExclusionSet {
        override fun contains(accessor: Accessor): Boolean = false
        override fun containsRead(accessor: Accessor): Boolean = false
        override fun containsWrite(accessor: Accessor): Boolean = false
        override fun addRead(accessor: Accessor): ExclusionSet = Concrete.ofRead(accessor)
        override fun addWrite(accessor: Accessor): ExclusionSet = Concrete.ofWrite(accessor)
        override fun union(other: ExclusionSet): ExclusionSet = other
        override fun intersect(other: ExclusionSet): ExclusionSet = this

        override fun toString(): String = "{}"
    }

    /**
     * No abstract tail at all, so there is no demand for a kind to describe: [Universe] is
     * kind-neutral and both merges return the other operand by reference.
     */
    data object Universe : ExclusionSet {
        override fun contains(accessor: Accessor): Boolean = true
        override fun containsRead(accessor: Accessor): Boolean = false
        override fun containsWrite(accessor: Accessor): Boolean = false
        override fun addRead(accessor: Accessor): ExclusionSet = this
        override fun addWrite(accessor: Accessor): ExclusionSet = this
        override fun union(other: ExclusionSet): ExclusionSet = this
        override fun intersect(other: ExclusionSet): ExclusionSet = other

        override fun toString(): String = "*"
    }

    /**
     * Stored as `(flat, write)` rather than `(read, write)`: the two are isomorphic
     * (`read = flat \ write`), but `flat` is what every consumer asks for, so [contains] stays a single
     * lookup and [flat] stays a field read.
     *
     * Invariants, enforced by [Concrete.create]: `flat` is non-empty and `write ⊆ flat`.
     */
    class Concrete private constructor(
        @JvmField val flat: PersistentSet<Accessor>,
        @JvmField val write: PersistentSet<Accessor>,
        private val hash: Int,
    ) : ExclusionSet {
        /** The accessors whose demand is [ExclusionKind.READ]. Computed; [flat] and [write] are stored. */
        val read: PersistentSet<Accessor> get() = flat.removeAll(write)

        override fun hashCode(): Int = hash

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is Concrete) return false

            if (hash != other.hash) return false
            return flat == other.flat && write == other.write
        }

        override fun contains(accessor: Accessor): Boolean = flat.contains(accessor)

        override fun containsRead(accessor: Accessor): Boolean =
            flat.contains(accessor) && !write.contains(accessor)

        override fun containsWrite(accessor: Accessor): Boolean = write.contains(accessor)

        override fun addRead(accessor: Accessor): ExclusionSet {
            // A read demand is subsumed by any demand already outstanding on the accessor.
            val flatWithAccessor = flat.add(accessor)
            if (flatWithAccessor === flat) return this

            return Concrete(flatWithAccessor, write, hash + FLAT_HASH_FACTOR * accessor.hashCode())
        }

        override fun addWrite(accessor: Accessor): ExclusionSet {
            val writeWithAccessor = write.add(accessor)
            if (writeWithAccessor === write) return this

            // Either a fresh demand, or a read demand promoted in place.
            val flatWithAccessor = flat.add(accessor)
            val hashDelta = if (flatWithAccessor === flat) 1 else FLAT_HASH_FACTOR + 1
            return Concrete(flatWithAccessor, writeWithAccessor, hash + hashDelta * accessor.hashCode())
        }

        override fun union(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> this
            Universe -> other
            is Concrete -> {
                val flatUnion = flat.addAll(other.flat)
                val writeUnion = write.addAll(other.write)
                if (flatUnion === flat && writeUnion === write) this else of(flatUnion, writeUnion)
            }
        }

        override fun intersect(other: ExclusionSet): ExclusionSet = when (other) {
            Empty -> other
            Universe -> this
            is Concrete -> {
                val flatIntersection = flat.retainAll(other.flat)
                if (flatIntersection.isEmpty()) {
                    Empty
                } else {
                    // (w₁ ∪ w₂) ∩ flat, but clamping each side BEFORE the union rather than after.
                    // `addAll` returns the receiver when it adds nothing, whereas adding an accessor
                    // and then retaining it away yields a set that is `equals` to the receiver but not
                    // `===` — which every storage using the `===` fixpoint signal reads as a change.
                    val writeIntersection = write.retainAll(flatIntersection)
                        .addAll(other.write.retainAll(flatIntersection))
                    if (flatIntersection === flat && writeIntersection === write) {
                        this
                    } else {
                        of(flatIntersection, writeIntersection)
                    }
                }
            }
        }

        override fun toString(): String = flat.joinToString(prefix = "{", postfix = "}") {
            if (it in write) "${it.toSuffix()}=" else it.toSuffix()
        }

        companion object {
            /**
             * `flat` and `write` must be hashed with different weights: a plain additive combination
             * would make `read={f}` and `write={f}` — precisely the pair this type exists to
             * distinguish — collide, in a value used as a hash-map key throughout every storage.
             */
            private const val FLAT_HASH_FACTOR = 31

            private fun hashOf(flat: PersistentSet<Accessor>, write: PersistentSet<Accessor>): Int =
                FLAT_HASH_FACTOR * flat.hashCode() + write.hashCode()

            private fun of(flat: PersistentSet<Accessor>, write: PersistentSet<Accessor>) =
                Concrete(flat, write, hashOf(flat, write))

            /** A demand on a single accessor. Named apart from the [Concrete.read]/[Concrete.write] fields. */
            fun ofRead(accessor: Accessor): Concrete =
                of(persistentHashSetOf(accessor), persistentHashSetOf())

            fun ofWrite(accessor: Accessor): Concrete =
                of(persistentHashSetOf(accessor), persistentHashSetOf(accessor))

            /**
             * Normalises to the invariants: an empty demand is [Empty], and `write` is clamped to
             * `flat` so the read/write partition stays disjoint by construction.
             */
            fun create(flat: PersistentSet<Accessor>, write: PersistentSet<Accessor>): ExclusionSet {
                if (flat.isEmpty()) return Empty
                return of(flat, write.retainAll(flat))
            }
        }
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import java.util.IdentityHashMap
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * `N{ f -> T , [any] -> S }  ==>  N{ [any] -> (S | T) }` for covered `f`.
 *
 * The operation ABSORBS rather than deletes, and that is the whole point. Deleting a subsumed
 * sibling is exact and still costs every finding, because the branch's contents are the names
 * `TreeInitialFactAbstraction` emits premises from. Merging the subtree into the `[any]` keeps
 * them AND moves them one level under the `[any]`, which is where R3b looks.
 *
 * Every case runs in BOTH manager arms -- see [Arm]. The rewrite is deliberately not gated on the
 * `[any]` unroll manager, so the manager's presence must be invisible to it in both directions: the
 * fold may not depend on a state being there, and it may not lose one that is.
 */
class SiblingAbsorptionTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val F = FieldAccessor("N", "f", "N")
    private val G = FieldAccessor("N", "g", "N")
    private val MARK = TaintMarkAccessor("test-mark")

    /**
     * An UNCOVERED accessor that may carry structure below it, which a taint mark may not
     * (`createRaw` rejects a mark above anything but a leaf, so `![m].[any]` is unconstructible).
     * It is the only way to build the shape [foldIsAFixpointUnderAnUncoveredAccessor] needs.
     */
    private val TYPE = TypeInfoAccessor("T")

    /**
     * One manager arm: the whole fixture, parameterised by `L`.
     *
     * The absorption tests used to run only at `L = -1`, where [AnyUnrollManager] is off entirely --
     * no state is allocated and every `AccessNode.anyId` is null. That silently excused the fold
     * from the node invariant `(anyId != null) == containsAnyAccessor()`, which is the one rule that
     * makes state propagation checkable at each construction site, and from every union the fold
     * performs when it merges two `[any]`-carrying subtrees. The second arm is where those bite.
     */
    private inner class Arm(anyUnrollLimit: Int) {
        val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), anyUnrollLimit)
        val base = AccessPathBase.This

        /** `<accessors>.*` -- open at the leaf, the production shape. */
        fun open(vararg accessors: Accessor): AccessTree.AccessNode {
            var f: FinalFactAp = manager.mostAbstractFinalAp(base)
            accessors.reversed().forEach { f = f.prependAccessor(it) }
            return (f as AccessTree).access
        }

        fun node(vararg branches: AccessTree.AccessNode): AccessTree.AccessNode {
            var n = manager.emptyNode
            branches.forEach { n = n.mergeAdd(it) }
            return n
        }

        fun premise(vararg accessors: Accessor): InitialFactAp {
            var p: InitialFactAp = manager.mostAbstractInitialAp(base)
            accessors.reversed().forEach { p = p.prependAccessor(it) }
            return p
        }

        fun idx(a: Accessor): Int = with(manager) { a.idx }

        fun AccessTree.AccessNode.render(): String =
            toString().replace('\n', ' ').trim()

        /**
         * The pass under test, plus the node invariant checked over the WHOLE result.
         *
         * Every case goes through here rather than calling the pass directly, so the invariant is
         * asserted on every shape the file builds instead of on the one somebody remembered to
         * check. `AccessNode`'s init block checks it at construction too -- this catches the case
         * where the fold hands back a node the constructor never saw, and it reports the offending
         * subtree rather than a stack from inside the factory.
         */
        fun AccessTree.AccessNode.fold(): AccessTree.AccessNode =
            compressAbsorbCoveredSiblings().also { it.assertAnyStateInvariant() }

        private fun AccessTree.AccessNode.assertAnyStateInvariant() {
            val seen = IdentityHashMap<AccessTree.AccessNode, Unit>()
            val pending = ArrayDeque(listOf(this))

            while (pending.isNotEmpty()) {
                val n = pending.removeLast()
                if (seen.put(n, Unit) != null) continue

                if (manager.anyUnroll.enabled) {
                    assertEquals(
                        n.containsAnyAccessor(), n.anyId != null,
                        "anyId/[any] edge mismatch after the fold at ${n.render()}",
                    )
                } else {
                    assertNull(n.anyId, "the manager is off, so no node may carry a state")
                }

                n.forEachAccessor { _, c -> pending.addLast(c) }
            }
        }
    }

    @Test
    fun `a covered sibling is folded into the any -- manager off`() =
        Arm(MANAGER_OFF).coveredSiblingIsFolded()

    @Test
    fun `a covered sibling is folded into the any -- manager on`() =
        Arm(MANAGER_ON).coveredSiblingIsFolded()

    private fun Arm.coveredSiblingIsFolded() {
        val n = node(open(F, G), open(AnyAccessor))          // { f.g.* , [any].* }
        assertTrue(n.contains(idx(F)), "precondition: the f edge is there")

        val c = n.fold()

        assertFalse(
            c.accessors!!.contains(idx(F)),
            "the covered `f` EDGE must be gone -- it is denoted by the [any]; got ${c.render()}",
        )
        assertTrue(c.accessors!!.contains(idx(AnyAccessor)), "the [any] survives")
    }

    @Test
    fun `a mark under a covered sibling is hoisted to directly under the any -- manager off`() =
        Arm(MANAGER_OFF).markIsHoistedUnderTheAny()

    @Test
    fun `a mark under a covered sibling is hoisted to directly under the any -- manager on`() =
        Arm(MANAGER_ON).markIsHoistedUnderTheAny()

    /**
     * The reason to absorb rather than delete. A mark buried under a covered sibling ends up
     * DIRECTLY below the `[any]`, which is the one place R3b enumerates.
     */
    private fun Arm.markIsHoistedUnderTheAny() {
        val n = node(open(F, MARK), open(AnyAccessor))       // { f.![m].* , [any].* }

        val c = n.fold()

        assertFalse(c.accessors!!.contains(idx(F)), "the `f` edge is absorbed")
        val anyChild = c.getChildForTest(idx(AnyAccessor))
        assertTrue(anyChild != null, "the [any] subtree survives")
        assertTrue(
            anyChild!!.accessors!!.contains(idx(MARK)),
            "the mark must now sit ONE level under the [any], where R3b enumerates; got ${c.render()}",
        )
    }

    @Test
    fun `an uncovered sibling is never absorbed -- manager off`() =
        Arm(MANAGER_OFF).uncoveredSiblingIsNeverAbsorbed()

    @Test
    fun `an uncovered sibling is never absorbed -- manager on`() =
        Arm(MANAGER_ON).uncoveredSiblingIsNeverAbsorbed()

    private fun Arm.uncoveredSiblingIsNeverAbsorbed() {
        val n = node(open(MARK), open(AnyAccessor))          // { ![m].* , [any].* }

        val c = n.fold()

        assertTrue(
            c.accessors!!.contains(idx(MARK)),
            "a taint mark is not denoted by [any] and must stay a literal edge; got ${c.render()}",
        )
    }

    @Test
    fun `without an any nothing moves, by identity -- manager off`() =
        Arm(MANAGER_OFF).withoutAnAnyNothingMoves()

    @Test
    fun `without an any nothing moves, by identity -- manager on`() =
        Arm(MANAGER_ON).withoutAnAnyNothingMoves()

    private fun Arm.withoutAnAnyNothingMoves() {
        val n = node(open(F, G), open(G))
        assertSame(n, n.fold(), "no [any] here, so nothing to absorb into")
    }

    @Test
    fun `the pass is idempotent by identity -- manager off`() =
        Arm(MANAGER_OFF).passIsIdempotentByIdentity()

    @Test
    fun `the pass is idempotent by identity -- manager on`() =
        Arm(MANAGER_ON).passIsIdempotentByIdentity()

    /**
     * Idempotence BY IDENTITY, which the storage layer requires: every storage decides "already
     * known" with `merged === stored`, so a pass that rebuilt an unchanged node would make every
     * re-derivation look new and re-propagate the whole tree.
     */
    private fun Arm.passIsIdempotentByIdentity() {
        val n = node(open(F, G), open(AnyAccessor), open(MARK))
        val once = n.fold()
        val twice = once.fold()
        assertSame(once, twice, "a second pass must return the very same object; got ${twice.render()}")
    }

    @Test
    fun `the fold is a fixpoint under an uncovered accessor -- manager off`() =
        Arm(MANAGER_OFF).foldIsAFixpointUnderAnUncoveredAccessor()

    @Test
    fun `the fold is a fixpoint under an uncovered accessor -- manager on`() =
        Arm(MANAGER_ON).foldIsAFixpointUnderAnUncoveredAccessor()

    /**
     * Regression: one pass is not a fixpoint, because the fold's MERGE can recreate the pattern.
     *
     * `{ f -> {T}.g.* , [any] -> {T}.[any].* }` folds to `{ [any] -> {T}.{ g -> * , [any] -> * } }`,
     * and the covered `g` is now a sibling of an `[any]` one level down. The intervening `{T}` is
     * UNCOVERED, so `normaliseUnderAny` -- which only walks covered-only paths, because that is
     * where its collapse is sound -- leaves it alone. A single-pass implementation therefore folds
     * again on the next call and hands the storage layer a rebuilt node for no new fact.
     */
    private fun Arm.foldIsAFixpointUnderAnUncoveredAccessor() {
        val n = node(open(F, TYPE, G), open(AnyAccessor, TYPE, AnyAccessor))
        val anyChild = n.getChildForTest(idx(AnyAccessor))
        assertTrue(
            anyChild?.getChildForTest(idx(TYPE))?.containsAnyAccessor() == true,
            "precondition: the [any] really does sit under the uncovered {T}; got ${n.render()}",
        )

        val once = n.fold()
        assertSame(once, once.fold(), "the pass must reach a fixpoint; got ${once.fold().render()}")
    }

    @Test
    fun `absorption widens the denotation and NARROWS what the fact can match -- manager off`() =
        Arm(MANAGER_OFF).absorptionNarrowsWhatTheFactCanMatch()

    @Test
    fun `absorption widens the denotation and NARROWS what the fact can match -- manager on`() =
        Arm(MANAGER_ON).absorptionNarrowsWhatTheFactCanMatch()

    /**
     * THE FALSIFIER, and the reason this ships off.
     *
     * The soundness argument -- `[any].(S|T)` denotes `<covered>*.(S|T)`, which contains `f.T` --
     * holds for the DENOTATION reader. It does NOT hold for the MATCHING reader, which has been the
     * default since literal `[any]` matching landed: `getChildMatching` keeps `literal(a)` and the
     * zero-step `any().literal(a)` and DROPS the synthesised term. Absorbing deletes the literal
     * `f` edge, and the zero-step read finds something deeper and different, so a premise naming
     * `f` stops selecting the branch.
     *
     * So the rewrite is a widening of what the fact DENOTES and a NARROWING of what it can MATCH.
     * That is the mechanism behind conductor going 2 findings -> 0 with absorption on, and it is
     * not visible in any denotational argument.
     */
    private fun Arm.absorptionNarrowsWhatTheFactCanMatch() {
        val fact = manager.mostAbstractFinalAp(base)
            .let { AccessTree(manager, base, node(open(F, G), open(AnyAccessor)), it.exclusions) }
        val premiseF = premise(F)

        assertTrue(
            fact.delta(premiseF).isNotEmpty(),
            "before: the literal `f` edge is there, so the premise selects it",
        )

        val compressed = AccessTree(manager, base, fact.access.fold(), fact.exclusions)

        assertTrue(
            compressed.delta(premiseF).isEmpty(),
            "after: `f` is denoted but no longer HELD, and the matching reader is literal -- so the " +
                "premise is refused. This is the cost, and it is invisible to the denotation argument.",
        )
    }

    private companion object {
        /** `L < 0`: [AnyUnrollManager] is off entirely, the pre-feature behaviour. */
        const val MANAGER_OFF = -1

        /** The frontier configuration's budget, so the second arm is the one production runs. */
        const val MANAGER_ON = 100
    }
}

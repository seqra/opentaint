package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import java.util.IdentityHashMap
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * The manager as the fact tree actually uses it: the branch invariant, the forced nested-`[any]`
 * collapse, the record/charge split between build and query callers, and the absorption a spent pot
 * performs instead of truncating.
 *
 * The branch invariant is the one to trust. Two managers reachable from one origin cost `k*L` and
 * heal as they meet; two managers on ONE root-to-leaf path cost `L^d` and never heal, because the
 * pots compound rather than add -- which is the exact failure the per-fact carried limit was
 * rejected for.
 */
class AnyUnrollFactTest {

    private companion object {
        val FIELD_F = FieldAccessor("Box", "f", "Box")
        val FIELD_G = FieldAccessor("Box", "g", "Box")
        val FIELD_H = FieldAccessor("Box", "h", "Box")

        val TYPE = TypeInfoAccessor("Box")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private var configuredLimit: Int = 1_000
    private var managerCreated = false

    private val manager: TreeApManager by lazy {
        managerCreated = true
        TreeApManager(UnrollStrategy, RefManager(), Cancellation(), configuredLimit)
    }

    private fun limit(value: Int) {
        check(!managerCreated) { "the limit must be chosen before the first fact is built" }
        configuredLimit = value
    }

    private val base = AccessPathBase.This

    private fun idx(accessor: Accessor) = with(manager) { accessor.idx }

    private fun concreteFact(vararg accessors: Accessor): AccessTree {
        var fact: FinalFactAp = manager.createFinalAp(base, ExclusionSet.Empty)
        for (accessor in accessors.reversed()) fact = fact.prependAccessor(accessor)
        return fact as AccessTree
    }

    private fun abstractFact(vararg accessors: Accessor): AccessTree {
        var fact: FinalFactAp = manager.mostAbstractFinalAp(base)
        for (accessor in accessors.reversed()) fact = fact.prependAccessor(accessor)
        return fact as AccessTree
    }

    private fun treeOf(node: AccessNode) = AccessTree(manager, base, node, ExclusionSet.Empty)

    /** Raw node construction; the array factory still normalises, which is what several tests check. */
    private fun node(vararg children: Pair<Accessor, AccessNode>): AccessNode {
        val sorted = children.map { idx(it.first) to it.second }.sortedBy { it.first }
        return manager.create(
            isAbstract = false, isFinal = false, null,
            sorted.map { it.first }.toIntArray(),
            sorted.map { it.second }.toTypedArray(),
            anyState = null,
        )
    }

    private fun premiseChain(vararg accessors: Accessor): AccessPath.AccessNode {
        val indices = IntArrayList()
        accessors.forEach { indices.add(idx(it)) }
        return manager.createNodeFromAccessors(indices)!!
    }

    private fun deltaOf(fact: AccessTree): FinalFactAp.Delta =
        fact.delta(manager.mostAbstractInitialAp(base)).single { !it.isEmpty }

    /* ---------- the two obligations, as walks over a built tree ---------- */

    /** Distinct managers on the worst root-to-leaf path. The gate is `<= 1`. */
    private fun maxManagersPerPath(node: AccessNode): Int {
        val worst = intArrayOf(0)
        walkPaths(node, mutableListOf(), worst, IdentityHashMap())
        return worst[0]
    }

    private fun walkPaths(
        node: AccessNode,
        onPath: MutableList<AnyUnrollState>,
        worst: IntArray,
        visiting: IdentityHashMap<AccessNode, Unit>,
    ) {
        if (visiting.put(node, Unit) != null) return

        val own = node.anyId?.find()
        if (own != null) onPath.add(own)

        val distinct = onPath.distinctBy { System.identityHashCode(it) }.size
        if (distinct > worst[0]) worst[0] = distinct

        node.forEachAccessor { _, child -> walkPaths(child, onPath, worst, visiting) }

        if (own != null) onPath.removeAt(onPath.size - 1)
        visiting.remove(node)
    }

    private fun anyStates(node: AccessNode): List<AnyUnrollState> {
        val out = mutableListOf<AnyUnrollState>()
        collect(node, out, IdentityHashMap())
        return out
    }

    private fun collect(node: AccessNode, out: MutableList<AnyUnrollState>, visited: IdentityHashMap<AccessNode, Unit>) {
        if (visited.put(node, Unit) != null) return
        node.anyId?.let { out.add(it) }
        node.forEachAccessor { _, child -> collect(child, out, visited) }
    }

    private fun assertOnePotPerBranch(node: AccessNode, message: String) {
        assertTrue(maxManagersPerPath(node) <= 1, "$message -- tree=$node")
        val dags = anyStates(node).map { it.find().dag.find() }.distinctBy { System.identityHashCode(it) }
        assertTrue(dags.size <= 1, "$message: expected one pot, got ${dags.size} -- tree=$node")
    }

    /* ---------- inertness with the feature off ---------- */

    @Test
    fun `with the manager off no node carries a state`() {
        limit(-1)

        val fact = concreteFact(FIELD_F, AnyAccessor, FIELD_G)

        assertFalse(manager.anyUnroll.enabled)
        assertTrue(anyStates(fact.access).isEmpty(), "L < 0 must allocate nothing at all")
        assertNull(fact.access.getChildRecordingForTest(idx(FIELD_F))?.anyId)
    }

    private fun AccessNode.getChildRecordingForTest(accessor: Int): AccessNode? = getChildRecording(accessor)

    /* ---------- identity ---------- */

    @Test
    fun `an any-free tree hashes and compares exactly as before`() {
        val plain = concreteFact(FIELD_F, FIELD_G)
        val same = concreteFact(FIELD_F, FIELD_G)

        assertNull(plain.access.anyId, "no [any] edge, no state")
        assertEquals(plain.access, same.access)
        assertEquals(plain.access.hashCode(), same.access.hashCode())
    }

    /**
     * A union moves the representative. If `hashCode` resolved it, every hash structure already
     * holding the node -- the interner's bucket map, the edge sets, the enqueued-unchanged set --
     * would silently lose the entry. So the STORED reference is what is hashed and compared, and
     * `find` appears only at build time and in the merge guard.
     */
    @Test
    fun `a union does not change a live node's hashCode`() {
        val left = concreteFact(AnyAccessor, FIELD_F)
        val right = concreteFact(AnyAccessor, FIELD_G)

        val leftState = assertNotNull(left.access.anyId)
        val rightState = assertNotNull(right.access.anyId)
        assertFalse(leftState === rightState, "two independent prepends are two origins")

        val hashBefore = left.access.hashCode()
        val equalBefore = left.access == left.access

        manager.anyUnroll.union(leftState, rightState)

        assertEquals(hashBefore, left.access.hashCode(), "the hash must not move under a union")
        assertTrue(equalBefore && left.access == left.access)
        assertSame(leftState, left.access.anyId, "the stored reference is untouched")
        assertSame(leftState.find(), rightState.find(), "while `find` sees the merge")
    }

    /* ---------- the branch invariant ---------- */

    @Test
    fun `two any edges separated by an uncovered accessor share one pot`() {
        // `[any].{Box}.[any].$` -- the collapse must NOT fire ({Box} is not covered, so `[any]` does
        // not range over it and collapsing would lose paths), but the pots must still be one.
        val fact = concreteFact(TYPE, AnyAccessor)
        val prepended = fact.prependAccessor(AnyAccessor) as AccessTree

        val belowNewAny = prepended.access.accessorNodes!!.single()
        assertTrue(belowNewAny.containsAnyInThisOrDeepNodes, "the [any] below {Box} must survive")

        val states = anyStates(prepended.access)
        assertEquals(2, states.size, "both edges are still there")
        assertOnePotPerBranch(prepended.access, "an uncovered accessor separates the edges but not the pots")
        assertSame(
            states[0].find(), states[1].find(),
            "the population under them is multiplicative, so they must spend from one pot"
        )
    }

    @Test
    fun `prepending any onto a covered chain collapses and unions`() {
        val fact = concreteFact(FIELD_F, FIELD_G, AnyAccessor)
        val inner = assertNotNull(anyStates(fact.access).singleOrNull())

        val prepended = fact.prependAccessor(AnyAccessor) as AccessTree

        assertEquals(listOf(ANY_ACCESSOR_IDX), prepended.access.accessors!!.toList())
        assertFalse(
            prepended.access.accessorNodes!!.single().containsAnyInThisOrDeepNodes,
            "no [any] may remain below the new [any] once the chain between them is covered-only"
        )

        val outer = assertNotNull(prepended.access.anyId)
        assertSame(inner.find(), outer.find(), "the collapsed edge's pot is absorbed, not discarded")
        assertOnePotPerBranch(prepended.access, "after a collapse")
    }

    /**
     * The graft under a CONCRETE parent edge: `parentEdgeIsAny` is a one-level memory, so absorption
     * is skipped and the delta lands verbatim under the receiver's concrete prefix. That is the most
     * executed graft in the engine and the single largest refill hole in the design.
     *
     * `concat` rebuilds the receiver's spine, so the outer `[any]` edge is RE-INSTALLED with the
     * grafted subtree already underneath it, and one normalisation sees the whole thing.
     */
    @Test
    fun `a graft below a concrete edge under an any is normalised and unioned`() {
        val receiver = abstractFact(AnyAccessor, FIELD_F)      // this.[any].f.*
        val donor = concreteFact(AnyAccessor, FIELD_G)         // this.[any].g.$

        val receiverState = assertNotNull(receiver.access.anyId)
        val donorState = assertNotNull(donor.access.anyId)
        assertFalse(receiverState.find() === donorState.find(), "two independent origins to start with")

        val result = assertNotNull(
            receiver.concat(FactTypeChecker.Dummy, deltaOf(donor)) as AccessTree?,
            "the graft must produce a fact"
        )

        assertOnePotPerBranch(result.access, "the graft must not leave two managers on one branch")
        assertSame(
            receiverState.find(), donorState.find(),
            "the delta's manager is carried across, never re-allocated"
        )
        assertFalse(
            result.access.accessorNodes!!.single().containsAnyInThisOrDeepNodes,
            "`f` is covered, so `[any].f.[any]` collapses at the point the edge is re-installed"
        )
    }

    /**
     * The second producer of the nested shape found by the census: summary compression deletes a
     * chain of accessors that lie in one SCC of the accessor graph, and that set MAY contain an
     * uncovered accessor -- so deleting it can bring an `[any]` up directly under another one.
     */
    @Test
    fun `removeAllAccessorChains cannot leave a nested any behind`() {
        val inner = node(AnyAccessor to manager.finalNode)              // [any].$
        val chain = node(FIELD_F to node(TYPE to inner))                // f.{Box}.[any].$
        val outer = node(AnyAccessor to chain)                          // [any].f.{Box}.[any].$

        assertEquals(2, anyStates(outer).size, "the fixture really does hold two edges")
        assertOnePotPerBranch(outer, "even un-collapsed, the pots are one")

        val scc = IntOpenHashSet().apply { add(idx(FIELD_F)); add(idx(TYPE)) }
        val compressed = outer.removeAllAccessorChains(
            scc, chainLengthToRemove = 2, cache = IdentityHashMap(), cancellation = Cancellation()
        )

        val belowOuter = assertNotNull(compressed.accessorNodes?.singleOrNull())
        assertFalse(
            belowOuter.containsAnyInThisOrDeepNodes,
            "deleting an uncovered accessor brought the inner [any] up; the normalisation must " +
                "collapse it rather than leave two edges on one branch -- got $compressed"
        )
        assertOnePotPerBranch(compressed, "after summary compression")
    }

    @Test
    fun `a merge of two any-carrying facts leaves one pot`() {
        val left = concreteFact(AnyAccessor, FIELD_F)
        val right = concreteFact(AnyAccessor, FIELD_G)

        val leftState = assertNotNull(left.access.anyId)
        val rightState = assertNotNull(right.access.anyId)

        val merged = left.access.mergeAdd(right.access)

        assertSame(leftState.find(), rightState.find(), "two [any] edges became one edge")
        assertOnePotPerBranch(merged, "after a position-wise merge")
    }

    /* ---------- the record, and the query that must not record ---------- */

    @Test
    fun `a covered read through an any records one accessor`() {
        val fact = abstractFact(AnyAccessor)                     // this.[any].*
        val state = assertNotNull(fact.access.anyId)
        assertEquals(0, manager.anyUnroll.totalOf(state))

        val read = assertNotNull(fact.readAccessor(FIELD_F) as AccessTree?)
        assertEquals(1, manager.anyUnroll.totalOf(state), "materialising `f` out of the `[any]` costs 1")

        // The residual is the same logical `[any]` with one covered step consumed, so it carries the
        // SUCCESSOR -- not the parent, which would let the automaton stay one level deep however
        // wide the fan-out.
        val residual = assertNotNull(read.access.anyId)
        assertFalse(residual === state, "the read advances the state")
        assertSame(residual.find(), state.find().children!!.get(idx(FIELD_F))!!.find())

        // Re-reading the same accessor is free: that is the termination argument, not an
        // optimisation.
        fact.readAccessor(FIELD_F)
        assertEquals(1, manager.anyUnroll.totalOf(state))

        fact.readAccessor(FIELD_G)
        assertEquals(2, manager.anyUnroll.totalOf(state), "a different accessor is a different path")
    }

    @Test
    fun `query callers record nothing`() {
        val fact = abstractFact(AnyAccessor)
        val state = assertNotNull(fact.access.anyId)

        // Each of these reaches `getChild`, and each answers a boolean. Charging them would trip the
        // cut early and coarsen facts that were never growing.
        fact.contains(AccessPath(manager, base, premiseChain(FIELD_F), ExclusionSet.Empty))
        fact.equalTo(AccessPath(manager, base, premiseChain(FIELD_F), ExclusionSet.Empty))
        fact.startsWithAccessor(FIELD_F)

        assertEquals(0, manager.anyUnroll.totalOf(state), "a query must not move the budget")
        assertNull(state.find().children?.get(idx(FIELD_G)), "and must not mint")
    }

    /* ---------- the absorption ---------- */

    /**
     * Refusal is ABSORPTION, not truncation. `X.[any]` already denotes `X.a....` for covered `a`, so
     * declining to write `a` above the `[any]` asserts MORE, not less -- which is why no value of
     * `L`, including 0, can lose a finding relative to no limit at all.
     */
    @Test
    fun `a spent pot absorbs the step instead of writing it`() {
        limit(0)

        val fact = abstractFact(AnyAccessor)                     // this.[any].*
        assertTrue(manager.anyUnroll.budgetExhausted(fact.access.anyId))

        val filtered = assertNotNull(
            fact.access.filterStartsWith(premiseChain(FIELD_F)),
            "the premise still matches -- absorption coarsens, it does not reject"
        )

        assertEquals(
            listOf(ANY_ACCESSOR_IDX), filtered.accessors!!.toList(),
            "the `f` step is absorbed into the `[any]` that already denotes it -- got $filtered"
        )
    }

    @Test
    fun `an unspent pot writes the step`() {
        val fact = abstractFact(AnyAccessor)

        val filtered = assertNotNull(fact.access.filterStartsWith(premiseChain(FIELD_F)))

        assertEquals(
            listOf(idx(FIELD_F)), filtered.accessors!!.toList(),
            "with budget left the spine keeps its concrete prefix -- got $filtered"
        )
    }

    /**
     * The soundness boundary of the split, which an earlier and simpler form of the absorption got
     * wrong: the node a read returns is generally a MERGE of the `[any]` branch and concrete
     * branches, and dropping the step across the whole node would rewrite `a.f.S` as `f.S` on the
     * concrete ones -- neither a superset nor a subset, so a genuine loss.
     */
    @Test
    fun `absorption keeps the step on branches an any does not denote`() {
        limit(0)

        val withConcrete = node(
            AnyAccessor to manager.abstractNode,
            FIELD_H to manager.finalNode,
        )

        val filtered = assertNotNull(treeOf(withConcrete).access.filterStartsWith(premiseChain(FIELD_H)))

        assertTrue(
            filtered.accessors!!.toList().contains(idx(FIELD_H)),
            "`h` is reached through a concrete edge, not through the `[any]`, so the step stays -- got $filtered"
        )
    }
}

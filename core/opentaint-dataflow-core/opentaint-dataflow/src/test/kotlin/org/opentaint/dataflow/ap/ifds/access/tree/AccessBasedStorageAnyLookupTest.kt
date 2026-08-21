package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.IntArrayList
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromAccessors
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Which PREMISES a caller fact activates in an [AccessBasedStorage] trie, for a fact that carries
 * `[any]`.
 *
 * Until `[any]` became representable in a premise, `children.get(ANY_ACCESSOR_IDX)` was always null,
 * so the only override of `collectNodesContainsAccessor` compensated with a blanket
 * `nodes += allNodes()` -- the whole premise subtree, pattern discarded. These tests pin the rule
 * that replaces it: a STRUCTURAL arm matching the trie's literal `[any]` key pattern-directed, and
 * an EXPANSION arm restricted to accessors `[any]` can actually step over.
 *
 * The rule mirrors `AccessTree.AccessNode.getChild`, which is what `AccessTree.delta` -- the exact
 * test applied downstream -- uses to decide whether an activated premise really applies. Anything
 * this lookup returns that `delta` rejects is wasted work; anything it fails to return is a lost
 * flow.
 */
class AccessBasedStorageAnyLookupTest {

    private companion object {
        val FIELD_X = FieldAccessor("Box", "x", "Box")
        val FIELD_Y = FieldAccessor("Box", "y", "Box")
        val FIELD_Z = FieldAccessor("Box", "z", "Box")

        val MARK = TaintMarkAccessor("m")
        val TYPE = TypeInfoAccessor("Box")
        val STATIC = ClassStaticAccessor("Box")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())

    private val base = AccessPathBase.This

    private fun idx(accessor: Accessor) = with(manager) { accessor.idx }

    /**
     * A storage whose payload is just the premise's own name, so a lookup result can be asserted as
     * a set of names.
     *
     * It deliberately adds NOTHING to [AccessBasedStorage]: the `[any]` rule lives in the base
     * traversal, so this bare subclass is representative of all three real storages, including the
     * two that never had an override.
     */
    private class NamedStorage(manager: TreeApManager) : AccessBasedStorage<NamedStorage>(manager) {
        var premise: String? = null

        override fun createStorage() = NamedStorage(manager)

        override fun printStorageNode(): String = premise.toString()
    }

    private fun chain(accessors: List<Accessor>): AccessPath.AccessNode? {
        if (accessors.isEmpty()) return null

        val indices = IntArrayList()
        accessors.forEach { indices.add(idx(it)) }
        return manager.createNodeFromAccessors(indices)
    }

    private fun name(accessors: List<Accessor>): String =
        if (accessors.isEmpty()) "<root>" else accessors.joinToString("") { it.toSuffix() }

    private fun trie(premises: List<List<Accessor>>): NamedStorage {
        val root = NamedStorage(manager)
        premises.forEach { root.getOrCreateNode(chain(it)).premise = name(it) }
        return root
    }

    /** A caller fact `this.a1.a2...$`, built through the public prepend path. */
    private fun fact(vararg accessors: Accessor): AccessTree.AccessNode {
        var tree = manager.createFinalAp(base, ExclusionSet.Empty)
        for (accessor in accessors.reversed()) {
            tree = tree.prependAccessor(accessor)
        }
        return (tree as AccessTree).access
    }

    private fun NamedStorage.activated(pattern: AccessTree.AccessNode): List<NamedStorage> =
        filterContains(pattern).toList()

    private fun NamedStorage.activatedNames(pattern: AccessTree.AccessNode): Set<String> =
        activated(pattern).mapNotNull { it.premise }.toSet()

    /* ---------- structural arm: a premise stored under a literal `[any]` key ---------- */

    @Test
    fun `a fact any activates a premise stored under a literal any key`() {
        val root = trie(
            listOf(
                listOf(AnyAccessor),
                listOf(AnyAccessor, FIELD_X),
            )
        )

        // this.[any].x.$ -- the sub-pattern below the fact's `[any]` is `x.$`
        val activated = root.activatedNames(fact(AnyAccessor, FIELD_X))

        assertTrue(name(listOf(AnyAccessor)) in activated, "the premise `[any]` is a prefix of the fact")
        assertTrue(name(listOf(AnyAccessor, FIELD_X)) in activated, "the premise `[any].x` matches the fact link for link")
    }

    @Test
    fun `the structural arm is pattern-directed, not a blanket`() {
        val root = trie(
            listOf(
                listOf(AnyAccessor, FIELD_X),
                listOf(AnyAccessor, MARK),
                listOf(AnyAccessor, FIELD_X, MARK),
            )
        )

        // this.[any].x.$ -- there is no mark anywhere in the fact
        val activated = root.activatedNames(fact(AnyAccessor, FIELD_X))

        assertTrue(name(listOf(AnyAccessor, FIELD_X)) in activated)
        assertTrue(
            name(listOf(AnyAccessor, MARK)) !in activated,
            "the old `allNodes()` blanket returned every premise below the `[any]`, mark or not"
        )
        assertTrue(name(listOf(AnyAccessor, FIELD_X, MARK)) !in activated, "nor does the pattern reach past its own end")
    }

    @Test
    fun `a mark below the fact any is matched literally through the structural arm`() {
        val root = trie(
            listOf(
                listOf(MARK),
                listOf(AnyAccessor, MARK),
                listOf(FIELD_X, MARK),
                listOf(FIELD_X, FIELD_Y, MARK),
            )
        )

        // this.[any].!m.$ -- `[any]` is zero-or-more, so every covered prefix carries the mark
        val activated = root.activatedNames(fact(AnyAccessor, MARK))

        assertEquals(
            setOf(
                name(listOf(MARK)),
                name(listOf(AnyAccessor, MARK)),
                name(listOf(FIELD_X, MARK)),
                name(listOf(FIELD_X, FIELD_Y, MARK)),
            ),
            activated
        )
    }

    /* ---------- expansion arm: concrete premises the `[any]` can step over ---------- */

    @Test
    fun `a fact any activates concrete premises reachable through covered accessors`() {
        val root = trie(
            listOf(
                emptyList(),
                listOf(FIELD_X),
                listOf(FIELD_X, FIELD_Y),
                listOf(FIELD_X, FIELD_Y, FIELD_Z),
                listOf(ElementAccessor),
                listOf(ElementAccessor, FIELD_X),
            )
        )

        // this.[any].$ -- whole subtree tainted, as far as `[any]` reaches
        val activated = root.activatedNames(fact(AnyAccessor))

        assertEquals(
            setOf(
                name(emptyList()),
                name(listOf(FIELD_X)),
                name(listOf(FIELD_X, FIELD_Y)),
                name(listOf(FIELD_X, FIELD_Y, FIELD_Z)),
                name(listOf(ElementAccessor)),
                name(listOf(ElementAccessor, FIELD_X)),
            ),
            activated
        )
    }

    @Test
    fun `expansion keeps the any in force, so it also reaches a deeper literal any premise`() {
        val root = trie(
            listOf(
                listOf(FIELD_X, AnyAccessor),
                listOf(FIELD_X, FIELD_Y, AnyAccessor, MARK),
            )
        )

        // this.[any].!m.$
        val activated = root.activatedNames(fact(AnyAccessor, MARK))

        assertTrue(name(listOf(FIELD_X, AnyAccessor)) in activated, "one expansion step, then the structural arm")
        assertTrue(
            name(listOf(FIELD_X, FIELD_Y, AnyAccessor, MARK)) in activated,
            "two expansion steps, then structural, then the mark"
        )
    }

    /* ---------- the narrowing: uncovered accessors are unreachable for an `[any]` ---------- */

    @Test
    fun `a fact any does not activate a premise behind a mark, type-info or static key`() {
        val premises = listOf(
            emptyList(),
            listOf(FIELD_X),
            listOf(MARK),
            listOf(FIELD_X, MARK),
            listOf(TYPE),
            listOf(FIELD_X, TYPE),
            listOf(STATIC),
            listOf(ValueAccessor),
            listOf(FinalAccessor),
        )
        val root = trie(premises)

        // this.[any].$ -- the sub-pattern below `[any]` is a bare `$`
        val activated = root.activatedNames(fact(AnyAccessor))

        assertEquals(
            setOf(name(emptyList()), name(listOf(FIELD_X)), name(listOf(FinalAccessor))),
            activated,
            "`[any]` covers fields and elements only; `$` fires because the sub-pattern is final"
        )

        val blanket = root.allNodes().mapNotNull { it.premise }.toSet()
        assertTrue(
            blanket.containsAll(activated) && blanket.size > activated.size,
            "the rule must be a strict subset of the `allNodes()` blanket it replaces"
        )
        premises.map { name(it) }.forEach { premise ->
            if (premise in activated) return@forEach
            assertTrue(premise in blanket, "everything dropped was returned by the old blanket")
        }
    }

    /* ---------- no duplicates ---------- */

    @Test
    fun `the lookup result contains no duplicates`() {
        val root = trie(
            listOf(
                emptyList(),
                listOf(FIELD_X),
                listOf(FIELD_X, FIELD_Y),
                listOf(AnyAccessor),
                listOf(AnyAccessor, FIELD_X),
                listOf(FIELD_X, AnyAccessor),
            )
        )

        // reaches the same node both structurally and by expansion, and re-adds the root at every level
        val activated = root.activated(fact(AnyAccessor, FIELD_X))

        assertEquals(
            activated.size,
            activated.distinct().size,
            "a repeated node would become a duplicate FactToFact edge"
        )
        assertEquals(1, activated.count { it === root }, "the root is added at every level of the walk")
    }

    @Test
    fun `a plain fact also never yields duplicates`() {
        val root = trie(listOf(emptyList(), listOf(FIELD_X), listOf(FIELD_X, FIELD_Y)))

        val activated = root.activated(fact(FIELD_X, FIELD_Y))

        assertEquals(activated.size, activated.distinct().size)
    }

    /* ---------- a non-`[any]` pattern is untouched ---------- */

    @Test
    fun `a non-any pattern activates exactly its prefixes, as before`() {
        val root = trie(
            listOf(
                emptyList(),
                listOf(FIELD_X),
                listOf(FIELD_X, FIELD_Y),
                listOf(FIELD_X, FIELD_Y, FinalAccessor),
                listOf(FIELD_X, FIELD_Z),
                listOf(FIELD_Y),
                listOf(FIELD_X, MARK),
            )
        )

        val activated = root.activatedNames(fact(FIELD_X, FIELD_Y))

        assertEquals(
            setOf(
                name(emptyList()),
                name(listOf(FIELD_X)),
                name(listOf(FIELD_X, FIELD_Y)),
                name(listOf(FIELD_X, FIELD_Y, FinalAccessor)),
            ),
            activated
        )
    }

    @Test
    fun `a plain fact does not reach a premise any -- the premise link needs a fact any to match`() {
        val root = trie(
            listOf(
                listOf(FIELD_X),
                listOf(AnyAccessor),
                listOf(FIELD_X, AnyAccessor),
            )
        )

        val activated = root.activatedNames(fact(FIELD_X))

        assertEquals(
            setOf(name(listOf(FIELD_X))),
            activated,
            "`AccessTree.AccessNode.getChild(ANY_ACCESSOR_IDX)` is null unless the fact has an `[any]`, " +
                    "so `delta` would reject these anyway"
        )
    }

    /* ---------- the rule is the base traversal's, not one storage's (design 6.7) ---------- */

    @Test
    fun `a storage that adds no override at all still gets both arms`() {
        // The shape of `FactSideEffectSummariesTreeApStorage` / `SideEffectRequirementTreeApStorage`:
        // before the rule was hoisted, an `[any]` fact activated the root and the literal `[any]`
        // key only, and every concrete side-effect premise below was silently missed.
        val root = trie(
            listOf(
                emptyList(),
                listOf(FIELD_X),
                listOf(FIELD_X, MARK),
                listOf(AnyAccessor, MARK),
            )
        )

        val activated = root.activatedNames(fact(AnyAccessor, MARK))

        assertEquals(
            setOf(
                name(emptyList()),
                name(listOf(FIELD_X)),
                name(listOf(FIELD_X, MARK)),
                name(listOf(AnyAccessor, MARK)),
            ),
            activated,
            "`x` and `x.!m` are reached only by the expansion arm"
        )
    }
}

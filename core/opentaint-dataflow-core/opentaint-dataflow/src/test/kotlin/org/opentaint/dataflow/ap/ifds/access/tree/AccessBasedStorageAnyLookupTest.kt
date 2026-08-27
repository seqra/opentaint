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
 * `nodes += allNodes()` -- the whole premise subtree, pattern discarded. The rule that replaced it
 * had THREE arms: ZERO-STEP (the `[any]` absorbs nothing, so the sub-pattern below it applies right
 * here), STRUCTURAL (the trie's literal `[any]` key, descended pattern-directed) and EXPANSION (the
 * `[any]` absorbs one covered step and stays in force below it, so every trie child keyed by an
 * accessor `[any]` can step over is re-entered with the SAME `[any]`-rooted pattern).
 *
 * **The expansion arm is gone under [TreeApManager.literalAnyMatch]** (2026-08-27, design
 * `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`). It was the one arm that
 * handed back a premise the fact does not hold LITERALLY, and it was the lookup half of a ratchet:
 * a premise link consumed without descending the fact is what lets `sum n!/(n-k)!` premises be
 * enumerated off a single `[any]`. `AccessTree.AccessNode.getChildMatching` -- the reader
 * `AccessTree.delta` and `filterStartsWith` now use -- dropped the matching term this arm mirrored,
 * so every premise the arm still produced would be refused downstream anyway.
 *
 * So these tests pin two arms and the ABSENCE of the third. The criterion is unchanged, because it
 * was never about the arm count: the rule mirrors the fact-side reader, so anything this lookup
 * returns that `delta` rejects is wasted work, and anything it fails to return is a lost flow. The
 * two cases whose entire subject WAS the expansion arm keep it pinned through
 * [synthesisingManager], for as long as the flag can still restore it.
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

    // An EXPLICIT limit. Without one this manager inherits `-Dopentaint.anyUnrollLimit` from the
    // Gradle JVM, which `configureDefaultTest` forwards into the forked test worker AND declares a
    // task input -- so these representation constraints would be silently sensitive to a knob, and a
    // gate run could not tell a regression from a setting. `-1` is the feature off, which is what
    // every assertion in this file is about.
    private val manager = TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1)

    /**
     * The same fixture read the PRE-2026-08-27 way: `literalAnyMatch = false` restores the
     * synthesising reader, and with it the EXPANSION arm of `collectNodesContainsAnyAccessor`.
     *
     * Only the two cases whose entire subject is that arm use this manager, so the file stays a
     * statement about the shipped rule with the ablation pinned beside it rather than a file with
     * two behaviours in it. When the flag goes, these companions go with it.
     */
    private val synthesisingManager =
        TreeApManager(UnrollStrategy, RefManager(), Cancellation(), -1, literalAnyMatch = false)

    private val base = AccessPathBase.This

    private fun TreeApManager.idxOf(accessor: Accessor) = accessor.idx

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

    private fun TreeApManager.chainOf(accessors: List<Accessor>): AccessPath.AccessNode? {
        if (accessors.isEmpty()) return null

        val indices = IntArrayList()
        accessors.forEach { indices.add(idxOf(it)) }
        return this.createNodeFromAccessors(indices)
    }

    private fun name(accessors: List<Accessor>): String =
        if (accessors.isEmpty()) "<root>" else accessors.joinToString("") { it.toSuffix() }

    private fun TreeApManager.trieOf(premises: List<List<Accessor>>): NamedStorage {
        val root = NamedStorage(this)
        premises.forEach { root.getOrCreateNode(chainOf(it)).premise = name(it) }
        return root
    }

    /** A caller fact `this.a1.a2...$`, built through the public prepend path. */
    private fun TreeApManager.factOf(vararg accessors: Accessor): AccessTree.AccessNode {
        var tree = createFinalAp(base, ExclusionSet.Empty)
        for (accessor in accessors.reversed()) {
            tree = tree.prependAccessor(accessor)
        }
        return (tree as AccessTree).access
    }

    // The whole file except the two expansion-arm companions reads through the shipped manager.
    private fun trie(premises: List<List<Accessor>>): NamedStorage = manager.trieOf(premises)

    private fun fact(vararg accessors: Accessor): AccessTree.AccessNode = manager.factOf(*accessors)

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

        // this.[any].!m.$ -- the mark is reached TWICE, once per surviving arm: with the `[any]`
        // taken zero times (`!m` hoisted up, which is the hoist R3b of `TreeInitialFactAbstraction`
        // depends on) and through the trie's own literal `[any]` key.
        val activated = root.activatedNames(fact(AnyAccessor, MARK))

        assertEquals(
            setOf(
                name(listOf(MARK)),
                name(listOf(AnyAccessor, MARK)),
            ),
            activated,
            "`x.!m` and `x.y.!m` sit behind concrete links the fact does not hold -- reaching them " +
                    "meant stepping the `[any]` over `x` and `y`, which is the expansion arm"
        )
    }

    /* ---------- the arm that is GONE: concrete premises the `[any]` could step over ---------- */

    /**
     * The expansion arm's own case, inverted. A premise reachable ONLY by stepping the `[any]` over
     * a covered accessor is a premise the fact does not hold literally, and it is no longer
     * activated -- however covered the accessors leading to it are, and however deep the chain.
     *
     * This is the lookup half of the ratchet: `x`, `x.y`, `x.y.z` off one `[any]` is the shape that
     * makes the premise count factorial in the demand set.
     */
    @Test
    fun `a fact any does not activate concrete premises reachable through covered accessors`() {
        val premises: List<List<Accessor>> = listOf(
            emptyList(),
            listOf(FIELD_X),
            listOf(FIELD_X, FIELD_Y),
            listOf(FIELD_X, FIELD_Y, FIELD_Z),
            listOf(ElementAccessor),
            listOf(ElementAccessor, FIELD_X),
        )

        // this.[any].$ -- the fact holds no concrete accessor of its own at all
        val activated = manager.trieOf(premises).activatedNames(manager.factOf(AnyAccessor))

        assertEquals(
            setOf(name(emptyList())),
            activated,
            "only the trie root, which is a literal prefix of every fact -- `x`, `x.y`, `x.y.z`, " +
                    "`[*]` and `[*].x` were reachable only by synthesising a step out of the `[any]`"
        )

        // ... and the arm itself, still pinned for as long as the flag can restore it.
        val underSynthesisingReader = synthesisingManager.trieOf(premises)
            .activatedNames(synthesisingManager.factOf(AnyAccessor))

        assertEquals(
            premises.map { name(it) }.toSet(),
            underSynthesisingReader,
            "`literalAnyMatch = false` restores the expansion arm exactly: the whole covered subtree"
        )
    }

    /**
     * The compounding half of the same arm: expansion kept the `[any]` in force below the step it
     * absorbed, so it could take several covered steps and then hand off to the structural arm. That
     * is what made the arm unbounded rather than one level deep, and none of it survives.
     */
    @Test
    fun `expansion is gone, so a literal any premise behind covered steps is not reached`() {
        val premises: List<List<Accessor>> = listOf(
            listOf(AnyAccessor),
            listOf(FIELD_X, AnyAccessor),
            listOf(FIELD_X, FIELD_Y, AnyAccessor, MARK),
        )

        // this.[any].!m.$
        val activated = manager.trieOf(premises).activatedNames(manager.factOf(AnyAccessor, MARK))

        assertEquals(
            setOf(name(listOf(AnyAccessor))),
            activated,
            "the structural arm still matches the trie's `[any]` key link for link; the two premises " +
                    "behind a concrete `x` / `x.y` needed the `[any]` to step over them first"
        )

        // ... and the arm itself, still pinned for as long as the flag can restore it.
        val underSynthesisingReader = synthesisingManager.trieOf(premises)
            .activatedNames(synthesisingManager.factOf(AnyAccessor, MARK))

        assertTrue(
            name(listOf(FIELD_X, AnyAccessor)) in underSynthesisingReader,
            "old reader: one expansion step, then the structural arm"
        )
        assertTrue(
            name(listOf(FIELD_X, FIELD_Y, AnyAccessor, MARK)) in underSynthesisingReader,
            "old reader: two expansion steps, then structural, then the mark"
        )
    }

    /* ---------- the narrowing, now total: no concrete premise is reachable for an `[any]` ------ */

    /**
     * The old rule already refused a premise behind an accessor `[any]` cannot step over -- a taint
     * mark, a static, a type-info accessor, `[value]`. The literal rule subsumes that narrowing:
     * coverage no longer decides anything here, because no concrete link is stepped over at all.
     * The uncovered premises stay in the trie so the original narrowing keeps its witness.
     */
    @Test
    fun `a fact any activates no concrete premise, covered accessor or not`() {
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
            setOf(name(emptyList()), name(listOf(FinalAccessor))),
            activated,
            "`\$` fires because the sub-pattern is final and the trie holds that link literally; `x` " +
                    "used to fire because `[any]` covers fields, and coverage no longer matters here"
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
    fun `a storage that adds no override at all still gets the zero-step and structural arms`() {
        // The shape of `FactSideEffectSummariesTreeApStorage` / `SideEffectRequirementTreeApStorage`.
        // The point of hoisting the rule into the base traversal survives the literal rule and is
        // what this pins: the two storages that never had an override get the SAME rule as the one
        // that did, rather than whatever falling through happens to produce.
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
                name(listOf(AnyAccessor, MARK)),
            ),
            activated,
            "`<root>` is a literal prefix of every fact and `[any].!m` matches link for link; " +
                    "`x` and `x.!m` were the expansion arm's, and the fact holds no `x`"
        )
    }
}

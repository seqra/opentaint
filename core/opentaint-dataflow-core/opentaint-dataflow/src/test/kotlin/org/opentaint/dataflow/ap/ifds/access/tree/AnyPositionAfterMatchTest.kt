package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import java.util.IdentityHashMap
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotSame
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * WHERE the `[any]` edge ends up after a matching operation consumes a covered premise link, under
 * each of the two `[any]` matching modes.
 *
 * ## Why this file exists
 *
 * `AccessNode.compressAbsorbCoveredSiblings` rewrites `N{ f -> T , [any] -> S }` into
 * `N{ [any] -> (S | T) }` for a covered `f`. On conductor it fires **528,602** times with
 * `literalAnyMatch = true` and **19** times with `literalAnyMatch = false` -- four orders of
 * magnitude for one boolean. A four-orders-of-magnitude gap deserves a mechanism, not a story, and
 * the story on offer was:
 *
 * > under the denotational reader the demanded accessor is SYNTHESISED out of the `[any]` and the
 * > `[any]` is REINSTALLED BELOW it, producing a chain `f.[any]...`; so the `[any]` and the covered
 * > accessor are never SIBLINGS at one node and the shape the fold rewrites is never created. Under
 * > the literal reader the `[any]` stays put beside the literal child and merges accumulate covered
 * > siblings beside it.
 *
 * **Half of that is right and the operative half is wrong**, and the tests below are arranged so
 * that each half can be read off separately.
 *
 * ## What the measurements in this file actually say
 *
 * 1. [theDenotationalReaderReinstallsTheAnyBelowTheDemandedAccessor] -- the chain claim is TRUE.
 *    `this.[any].*` matched against the premise `this.f` yields `this.f.[any].*`. Zero nodes own
 *    both an `[any]` and a covered sibling; the `[any]` sits strictly below `f`. The fold is the
 *    identity on it.
 *
 * 2. [theLiteralReaderRefusesTheMatchOutright] -- but the *contrast* the story draws is not the one
 *    that exists. Under the literal reader the `[any]` does not "stay put beside the literal
 *    child": the operation produces NOTHING AT ALL. `delta` returns an empty list and
 *    `filterStartsWith` returns null, because [AccessTree.AccessNode.getChildMatching] keeps only
 *    `literal(f)` and the zero-step `any().literal(f)`, and an abstract `[any]` subtree has neither.
 *    So the mode difference at the reader is *whether a match happens*, not *where the `[any]` lands*.
 *
 * 3. [theWritebackRecreatesTheSiblingShapeUnderTheDenotationalReader] -- **the falsifier.** The
 *    claim "the shape the fold rewrites is never created" is FALSE. The chain is created inside one
 *    match; the sibling is created one step later, when the edge store merges that chain back beside
 *    the `[any]` it was read through. `{ f -> {[any] -> *} , [any] -> * }` is exactly the fold's
 *    input pattern, the fold does fire, and it collapses the whole thing back to `[any].*`. So the
 *    denotational round trip *manufactures* fold work, one covered literal edge per match.
 *
 * 4. [theFoldsInputShapesAreIdenticalInBothModes] -- and the fold is mode-blind. Every shape it
 *    actually rewrites here is produced by `mergeAdd` putting a literal covered branch beside an
 *    `[any]`, and that path never consults [TreeApManager.literalAnyReader]. Same input bytes, same
 *    output bytes, same identity verdict, in all four arms.
 *
 * 5. [theRoundTripAnalogueOfTheProductionCounter] -- the unit-level analogue of the production
 *    counter, and it points the OTHER WAY: 3 fold-rewritable nodes manufactured per three round
 *    trips under the denotational reader, 0 under the literal one.
 *
 * **Conclusion the file pins:** the 528,602-vs-19 gap is NOT explained by the position of the
 * `[any]` after a match. At the node level the denotational reader creates strictly MORE
 * fold-rewritable shapes per match than the literal one, because the literal one creates none. The
 * gap must therefore be a property of the fact POPULATION each mode drives the engine to store --
 * which premises `TreeInitialFactAbstraction` emits (`dropR3c`/`dropR4`, its R3c/R4 ladder) and
 * which of them the storage lookup answers (`AccessBasedStorage.kt:150`) -- and not of what one
 * matching operation does to one `[any]` edge. Anyone reaching for the position story to explain
 * the counter should read test 3 first.
 *
 * The single line that produces every difference this file observes is
 * `AccessTree.kt:784` -- `if (!manager.literalAnyReader) return getChild(accessor, record = true)`.
 * Everything else on both paths is shared code.
 *
 * ## Reading the rendered shapes
 *
 * Every test prints what it built and what it got. The renderer writes an open leaf as a slash and
 * a star, so `this.f.[any]` followed by an open leaf prints as `.f.[any]` plus that marker; two
 * space separated groups on one line are two branches of the same node. The prints are the point as much
 * as the assertions are -- the assertions pin the census, the prints let a human check that the
 * census is counting the shape they think it is.
 */
class AnyPositionAfterMatchTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            accessor is FieldAccessor || accessor is ElementAccessor
    }

    /** Covered: the strategy above unrolls fields, so `[any]` denotes it. */
    private val F = FieldAccessor("N", "f", "N")
    private val G = FieldAccessor("N", "g", "N")

    /** A covered spine field, so the `[any]` can be put somewhere other than the fact's root. */
    private val X = FieldAccessor("N", "x", "N")

    /**
     * UNCOVERED, and the reason the fold has anything to preserve: a taint mark is a name an
     * `[any]` can never denote, so a branch carrying one cannot simply be deleted as subsumed.
     */
    private val MARK = TaintMarkAccessor("test-mark")

    /**
     * Where the `[any]` edges of a tree sit, counted structurally rather than matched as text.
     *
     * [siblingNodes] is the fold's precondition, counted directly: a node owning an `[any]` edge AND
     * at least one covered edge of its own is exactly `N{ f -> T , [any] -> S }`.
     * [anyBelowCovered] is the competing shape: an `[any]`-owning node reached through a covered
     * edge, i.e. the `f.[any]...` chain. The two are independent -- a tree can have both -- which is
     * why they are separate counters and not a verdict.
     */
    private data class Census(
        val anyOwners: Int,
        val siblingNodes: Int,
        val anyBelowCovered: Int,
        val coveredEdges: Int,
    )

    /**
     * One fixture, parameterised by the two booleans that could plausibly matter.
     *
     * `literalAnyMatch` is the subject. `anyUnrollLimit` is a control: the absorbing prepend and the
     * `[any]` unroll automaton only exist when the manager is on, and either could in principle move
     * an `[any]` during the writeback (`installAbove` rewrites `f.[any].S` to `[any].S` when its
     * targeting allows). Every positional claim here is therefore asserted in both, so that "the
     * manager did it" is excluded rather than assumed away.
     */
    private inner class Arm(val literalAnyMatch: Boolean, val anyUnrollLimit: Int) {
        val manager = TreeApManager(
            UnrollStrategy, RefManager(), Cancellation(), anyUnrollLimit,
            literalAnyMatch = literalAnyMatch,
        )

        val base = AccessPathBase.This

        init {
            // Field indices come from a per-manager interner counter, so an accessor's index -- and
            // therefore the order branches print in -- depends on the order the fixture first asks
            // for it. Pinning that order here is what makes the cross-arm string comparison in
            // `theFoldsInputShapesAreIdenticalInBothModes` a statement about the trees rather than
            // about which test method ran first.
            listOf(F, G, X, MARK, AnyAccessor).forEach { idx(it) }
        }

        val label: String
            get() = "literalAnyMatch=$literalAnyMatch, L=$anyUnrollLimit"

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

        fun tree(n: AccessTree.AccessNode) = AccessTree(manager, base, n, ExclusionSet.Empty)

        fun idx(a: Accessor): Int = with(manager) { a.idx }

        fun AccessTree.AccessNode.render(): String = toString().replace('\n', ' ').trim()

        /** The summary-application matcher: consume the premise, keep the remainder. */
        fun deltaOf(fact: AccessTree.AccessNode, p: InitialFactAp): List<FinalFactAp.Delta> =
            tree(fact).delta(p)

        fun deltaNodes(fact: AccessTree.AccessNode, p: InitialFactAp): List<AccessTree.AccessNode> =
            deltaOf(fact, p).mapNotNull { (it as? AccessTree.NodeAccessTreeDelta)?.node }

        /** The subscription matcher: consume the premise, keep the WHOLE matched prefix plus tail. */
        fun filterStartsWith(fact: AccessTree.AccessNode, p: InitialFactAp): AccessTree.AccessNode? =
            fact.filterStartsWith((p as AccessPath).access)

        /**
         * What the edge stores do with a match result: put it back under the accessor the premise
         * consumed and merge it into the stored tree.
         *
         * `addParent` is the node-level `prependAccessor`, and `mergeAdd` is verbatim what
         * `MethodEdgesFinalTreeApSet` and `MethodEdgesInitialToFinalTreeApSet` call one line before
         * they call the fold.
         */
        fun writeBack(
            store: AccessTree.AccessNode,
            result: AccessTree.AccessNode,
            vararg prefix: Accessor,
        ): AccessTree.AccessNode {
            var n = result
            prefix.reversed().forEach { n = n.addParent(idx(it)) }
            return store.mergeAdd(n)
        }

        fun census(root: AccessTree.AccessNode): Census {
            var anyOwners = 0
            var siblings = 0
            var belowCovered = 0
            var coveredEdges = 0
            val anyIdx = idx(AnyAccessor)
            val seen = IdentityHashMap<AccessTree.AccessNode, Unit>()
            // `reachedViaCovered` is a property of the EDGE that got here, not of the node, so it
            // travels on the stack. A node shared by two parents is visited once and classified by
            // whichever edge reached it first; nothing in this file builds such a tree, and the
            // `anyOwners` total is the guard that would notice if something did.
            val pending = ArrayDeque(listOf(root to false))
            while (pending.isNotEmpty()) {
                val (n, reachedViaCovered) = pending.removeLast()
                if (seen.put(n, Unit) != null) continue

                var hasAny = false
                var hasCoveredSibling = false
                n.forEachAccessor { a, child ->
                    val covered = a != anyIdx && manager.isCoveredByAny(a)
                    if (a == anyIdx) hasAny = true
                    if (covered) {
                        hasCoveredSibling = true
                        coveredEdges++
                    }
                    pending.addLast(child to covered)
                }

                if (hasAny) {
                    anyOwners++
                    if (hasCoveredSibling) siblings++
                    if (reachedViaCovered) belowCovered++
                }
            }
            return Census(anyOwners, siblings, belowCovered, coveredEdges)
        }

        /** The pass under test. Returns the result; the caller decides what identity means. */
        fun AccessTree.AccessNode.fold(): AccessTree.AccessNode = compressAbsorbCoveredSiblings()

        fun show(what: String, n: AccessTree.AccessNode?) {
            if (n == null) {
                println("  [$label] $what => <no match>")
                return
            }
            val folded = n.fold()
            println("  [$label] $what => ${n.render()}")
            println("      census=${census(n)}  foldChanged=${folded !== n}  folded=${folded.render()}")
        }
    }

    // ---------------------------------------------------------------- 1. the chain claim: TRUE

    @Test
    fun `the denotational reader reinstalls the any below the demanded accessor -- manager off`() =
        Arm(literalAnyMatch = false, anyUnrollLimit = MANAGER_OFF)
            .theDenotationalReaderReinstallsTheAnyBelowTheDemandedAccessor()

    @Test
    fun `the denotational reader reinstalls the any below the demanded accessor -- manager on`() =
        Arm(literalAnyMatch = false, anyUnrollLimit = MANAGER_ON)
            .theDenotationalReaderReinstallsTheAnyBelowTheDemandedAccessor()

    /**
     * The confirmed half of the hypothesis, pinned at both matching entry points.
     *
     * `getChild` synthesises `f` out of the `[any]`, clears `f` from the `[any]` subtree so the step
     * cannot repeat, and RE-INSTALLS the `[any]` under the synthesised accessor
     * (`AccessTree.kt:833-838`). `filterStartsWith` then rebuilds the spine it walked, so the
     * accessor lands ABOVE the reinstalled `[any]` and the result is a chain: `this.f.[any].*`.
     *
     * The census is the assertion, not the string: zero nodes own an `[any]` beside a covered edge,
     * exactly one `[any]` sits below a covered accessor. And the fold is the identity on a chain,
     * which is the point -- a chain gives it nothing to do.
     */
    private fun Arm.theDenotationalReaderReinstallsTheAnyBelowTheDemandedAccessor() {
        val fact = open(AnyAccessor)                                  // this.[any].*
        val p = premise(F)                                            // this.f
        println("[$label] chain claim: fact=${fact.render()} premise=$p")

        val matched = filterStartsWith(fact, p)
        show("filterStartsWith(this.f)", matched)
        assertTrue(
            matched != null,
            "precondition: the denotational reader synthesises `f` out of the [any], so the " +
                "subscription matcher must match; it returned nothing",
        )

        val c = census(matched!!)
        assertEquals(
            0, c.siblingNodes,
            "THE CHAIN CLAIM: no node may own both an [any] and a covered sibling after the " +
                "denotational match -- the [any] was reinstalled BELOW `f`, not left beside it. " +
                "Got ${matched.render()}",
        )
        assertEquals(
            1, c.anyBelowCovered,
            "and the [any] must sit strictly below the covered accessor the premise named. " +
                "Got ${matched.render()}",
        )
        assertEquals(
            1, c.coveredEdges,
            "exactly one covered edge, the `f` the spine rebuild wrote back above the [any]",
        )

        assertSame(
            matched, matched.fold(),
            "the fold is the IDENTITY on a chain -- this is the unit-level analogue of the `19` " +
                "half of the 528,602-vs-19 counter, and it is real as far as it goes",
        )

        // The same claim at the other matching entry point. `delta` keeps only the REMAINDER, so
        // there is no spine to rebuild and the `[any]` comes back at the remainder's own root --
        // still not beside a covered edge, and still nothing for the fold to do.
        val deltas = deltaNodes(fact, p)
        assertEquals(1, deltas.size, "delta must produce exactly one remainder here; got $deltas")
        show("delta(this.f) remainder", deltas.single())
        assertEquals(
            0, census(deltas.single()).siblingNodes,
            "the delta remainder carries the [any] at its own root, with no covered sibling; " +
                "got ${deltas.single().render()}",
        )
        assertSame(
            deltas.single(), deltas.single().fold(),
            "so the fold is the identity on the remainder too",
        )
    }

    // ------------------------------------------------- 2. the contrast is not the claimed one

    @Test
    fun `the literal reader refuses the match outright -- manager off`() =
        Arm(literalAnyMatch = true, anyUnrollLimit = MANAGER_OFF).theLiteralReaderRefusesTheMatchOutright()

    @Test
    fun `the literal reader refuses the match outright -- manager on`() =
        Arm(literalAnyMatch = true, anyUnrollLimit = MANAGER_ON).theLiteralReaderRefusesTheMatchOutright()

    /**
     * Under the literal reader the `[any]` does not "stay put beside the literal child". There IS no
     * result: [AccessTree.AccessNode.getChildMatching] keeps `literal(f)` and the zero-step
     * `any().literal(f)` and drops the synthesised term, and `this.[any].*` has neither a literal
     * `f` edge nor an `f` child under its `[any]`, so the read returns null and both matchers refuse.
     *
     * This is the honest form of the contrast: the two modes do not put the `[any]` in two different
     * places, one of them puts it nowhere because it declines the premise. Every downstream
     * difference in stored shape therefore comes from WHICH premises get consumed, not from where a
     * consumed one leaves the edge.
     */
    private fun Arm.theLiteralReaderRefusesTheMatchOutright() {
        val fact = open(AnyAccessor)
        val p = premise(F)
        println("[$label] refusal: fact=${fact.render()} premise=$p")

        assertNull(
            filterStartsWith(fact, p),
            "the literal reader must refuse a premise naming an accessor the fact only DENOTES; " +
                "a non-null result would mean the synthesising term survived",
        )
        show("filterStartsWith(this.f)", filterStartsWith(fact, p))

        assertTrue(
            deltaOf(fact, p).isEmpty(),
            "and `delta` must refuse it too -- both matchers go through the same reader at " +
                "AccessTree.kt:784, so a disagreement would mean one of them bypassed it",
        )

        // Same at depth, so the refusal is not an artefact of the `[any]` sitting at the root.
        val deep = open(X, AnyAccessor)                               // this.x.[any].*
        assertNull(
            filterStartsWith(deep, premise(X, F)),
            "the refusal holds wherever the [any] sits; got a match on ${deep.render()}",
        )
        show("filterStartsWith(this.x.f) on this.x.[any].*", filterStartsWith(deep, premise(X, F)))
    }

    // ------------------------------------------------------------------ 3. THE FALSIFIER

    @Test
    fun `the writeback recreates the sibling shape under the denotational reader -- manager off`() =
        Arm(literalAnyMatch = false, anyUnrollLimit = MANAGER_OFF)
            .theWritebackRecreatesTheSiblingShapeUnderTheDenotationalReader()

    @Test
    fun `the writeback recreates the sibling shape under the denotational reader -- manager on`() =
        Arm(literalAnyMatch = false, anyUnrollLimit = MANAGER_ON)
            .theWritebackRecreatesTheSiblingShapeUnderTheDenotationalReader()

    /**
     * **This is the test that refutes the hypothesis, and it is deliberately the loudest one here.**
     *
     * The claim was that under the denotational reader "the `[any]` and the covered accessor are
     * never SIBLINGS at one node, and the shape the fold rewrites is never created". The chain is
     * real (test 1) but it is not the end of the operation. The edge stores do not keep match
     * results on their own -- they MERGE them into the stored tree, and the stored tree still holds
     * the `[any]` the match was read through. Merging `f.[any].*` into `[any].*` gives
     *
     * ```
     * { f -> {[any] -> *} , [any] -> * }
     * ```
     *
     * which is `N{ f -> T , [any] -> S }` verbatim. The fold fires and collapses it straight back to
     * `[any].*`, i.e. the denotational round trip creates one unit of fold work per match and the
     * fold undoes it exactly.
     *
     * Nothing here is exotic: `mergeAdd` is the same call the two edge stores make one line before
     * `compressAbsorbCoveredSiblings`, and `addParent` is the same `prependAccessor` the fact API
     * exposes. The `[any]` suffix trim inside `mergeAdd` (`foldToAny = true`) does not prevent it --
     * it does not treat `f.[any].*` as subsumed by `[any].*`.
     *
     * So the position of the `[any]` after a match does not explain the production counter. If
     * anything it predicts the opposite sign.
     */
    private fun Arm.theWritebackRecreatesTheSiblingShapeUnderTheDenotationalReader() {
        val store = open(AnyAccessor)                                 // this.[any].*
        val matched = filterStartsWith(store, premise(F))
            ?: error("precondition: the denotational reader must match here")

        assertEquals(
            0, census(matched).siblingNodes,
            "precondition: the match result on its own is a chain, not a sibling shape",
        )

        val merged = store.mergeAdd(matched)
        show("store.mergeAdd(filterStartsWith result)", merged)

        assertEquals(
            1, census(merged).siblingNodes,
            "THE FALSIFIER: merging the chain back beside the [any] it was read through DOES " +
                "create `N{ f -> T, [any] -> S }`. The hypothesis said this shape is never built " +
                "under the denotational reader. Got ${merged.render()}",
        )
        assertNotSame(
            merged, merged.fold(),
            "and the fold therefore FIRES on it, in the mode that is supposed to give it nothing " +
                "to do; got ${merged.fold().render()}",
        )
        assertEquals(
            0, census(merged.fold()).siblingNodes,
            "the fold's own postcondition, for completeness: no sibling shape survives it",
        )

        // The delta channel, re-attached the way summary application re-attaches a remainder.
        val remainder = deltaNodes(store, premise(F)).single()
        val writtenBack = writeBack(store, remainder, F)
        show("store.mergeAdd(delta remainder prepended with f)", writtenBack)
        assertEquals(
            1, census(writtenBack).siblingNodes,
            "same through `delta`: prepending the consumed accessor and merging rebuilds the " +
                "sibling shape; got ${writtenBack.render()}",
        )

        // And it is not an artefact of the `[any]` being an abstract leaf: a name-critical mark
        // under the `[any]` -- the case the fold exists to preserve -- behaves identically.
        val markedStore = open(AnyAccessor, MARK)                     // this.[any].![m].*
        val markedMatch = filterStartsWith(markedStore, premise(F))
            ?: error("precondition: the denotational reader must match here too")
        val markedMerged = markedStore.mergeAdd(markedMatch)
        show("marked store.mergeAdd(match)", markedMerged)
        assertEquals(
            1, census(markedMerged).siblingNodes,
            "the same round trip on `this.[any].![m].*` also rebuilds the sibling shape; " +
                "got ${markedMerged.render()}",
        )
    }

    // ---------------------------------------------------- 4. the fold's input is mode-blind

    @Test
    fun `the fold's input shapes are identical in both modes -- manager off`() =
        theFoldsInputShapesAreIdenticalInBothModes(MANAGER_OFF)

    @Test
    fun `the fold's input shapes are identical in both modes -- manager on`() =
        theFoldsInputShapesAreIdenticalInBothModes(MANAGER_ON)

    /**
     * The control that closes the "maybe the shapes differ somewhere else" escape.
     *
     * Every sibling shape the fold actually rewrites in this file is produced by `mergeAdd` putting
     * a literal covered branch beside an `[any]`, and that path never consults
     * [TreeApManager.literalAnyReader] -- the mode is read in exactly three places
     * (`AccessTree.kt:784`, and the two `maxDepth` prefilters at `AccessTree.kt:2750` and `:2791`),
     * none of which is on it. So the same construction in the two modes must give the same tree, the
     * same fold result, and the same identity verdict, edge for edge.
     *
     * Three shapes, chosen to exercise the three outcomes the fold has: a covered sibling absorbed
     * into an abstract `[any]`; a covered sibling carrying a name-critical mark, which is the case
     * absorption exists to preserve; and a covered sibling merged into an `[any]` that already has
     * structure of its own, where the merge -- not the deletion -- is what is being checked.
     */
    private fun theFoldsInputShapesAreIdenticalInBothModes(anyUnrollLimit: Int) {
        val literal = Arm(literalAnyMatch = true, anyUnrollLimit = anyUnrollLimit)
        val denotational = Arm(literalAnyMatch = false, anyUnrollLimit = anyUnrollLimit)

        fun Arm.shapes(): List<Pair<String, AccessTree.AccessNode>> = listOf(
            "sibling over an abstract [any]" to node(open(F, G), open(AnyAccessor)),
            "literal branch merged beside a marked [any]" to open(AnyAccessor, MARK).mergeAdd(open(F, MARK)),
            "sibling over an [any] with its own structure" to node(open(F, MARK), open(AnyAccessor, G, MARK)),
        )

        val a = with(literal) { shapes() }
        val b = with(denotational) { shapes() }

        for (i in a.indices) {
            val (name, litNode) = a[i]
            val (_, denNode) = b[i]
            with(literal) { show("mode-blind[$i] $name", litNode) }
            with(denotational) { show("mode-blind[$i] $name", denNode) }

            assertEquals(
                with(literal) { litNode.render() }, with(denotational) { denNode.render() },
                "the CONSTRUCTION is mode-blind: `mergeAdd` never reads literalAnyReader, so the " +
                    "two modes must build the same tree for `$name`",
            )
            assertEquals(
                with(literal) { census(litNode) }.siblingNodes,
                with(denotational) { census(denNode) }.siblingNodes,
                "so the fold's precondition holds equally in both modes for `$name`",
            )
            assertEquals(
                with(literal) { litNode.fold().render() },
                with(denotational) { denNode.fold().render() },
                "and the FOLD is mode-blind: `compressAbsorbCoveredSiblings` reads only " +
                    "`isCoveredByAny`, which is the unroll strategy and not the matching mode",
            )
            assertEquals(
                with(literal) { litNode.fold() !== litNode },
                with(denotational) { denNode.fold() !== denNode },
                "including the identity verdict, which is what the production counter counts",
            )
        }
    }

    // ------------------------------- 5. the unit-level analogue of the production counter

    @Test
    fun `the round-trip analogue of the production counter -- manager off`() =
        theRoundTripAnalogueOfTheProductionCounter(MANAGER_OFF)

    @Test
    fun `the round-trip analogue of the production counter -- manager on`() =
        theRoundTripAnalogueOfTheProductionCounter(MANAGER_ON)

    /**
     * The closest thing to the production measurement that a unit test can honestly build, and it
     * comes out with the opposite sign.
     *
     * Three facts, one round trip each -- match a covered premise, put the result back where it came
     * from, merge it into the store -- and count the stores whose merged tree the fold rewrites.
     * That is exactly what `MethodEdgesFinalTreeApSet:45` and
     * `MethodEdgesInitialToFinalTreeApSet:108` do, minus the rest of the engine.
     *
     * Denotational: **3 of 3**. Literal: **0 of 3**, because no premise is consumed at all and the
     * store is returned by identity. So per matching operation the DENOTATIONAL reader manufactures
     * fold work and the literal one manufactures none -- while production reports 528,602 fold
     * firings under literal against 19 under denotational.
     *
     * The two are only consistent if the production gap is driven by the number and shape of facts
     * each mode makes the engine STORE, not by what one match does to one `[any]`. That is a claim
     * about `TreeInitialFactAbstraction`'s premise ladder (`dropR3c`, `dropR4`) and about
     * `AccessBasedStorage.kt:150`, and it is not testable at this level -- which is precisely why
     * pinning the negative result here is worth doing: it removes the position story from the list
     * of candidate explanations instead of leaving it as a plausible one.
     */
    private fun theRoundTripAnalogueOfTheProductionCounter(anyUnrollLimit: Int) {
        fun Arm.roundTripsThatCreateFoldWork(): Int {
            val cases = listOf(
                open(AnyAccessor) to premise(F),                       // this.[any].*      / this.f
                open(X, AnyAccessor) to premise(X, F),                 // this.x.[any].*    / this.x.f
                open(AnyAccessor, MARK) to premise(F),                 // this.[any].![m].* / this.f
            )
            var foldWork = 0
            for ((store, p) in cases) {
                val matched = filterStartsWith(store, p)
                if (matched == null) {
                    show("roundTrip(${store.render()} , $p) -- refused", null)
                    continue
                }
                val merged = store.mergeAdd(matched)
                show("roundTrip(${store.render()} , $p)", merged)
                if (merged.fold() !== merged) foldWork++
            }
            return foldWork
        }

        val literal = with(Arm(literalAnyMatch = true, anyUnrollLimit = anyUnrollLimit)) { roundTripsThatCreateFoldWork() }
        val denotational = with(Arm(literalAnyMatch = false, anyUnrollLimit = anyUnrollLimit)) { roundTripsThatCreateFoldWork() }
        println("fold-rewritable stores after one round trip each: literal=$literal denotational=$denotational")

        assertEquals(
            0, literal,
            "under the literal reader no premise is consumed, so nothing is written back and no " +
                "store acquires a sibling shape -- the fold has zero work to do per match",
        )
        assertEquals(
            3, denotational,
            "under the denotational reader every one of the three round trips leaves the store " +
                "holding `N{ f -> T, [any] -> S }` for the fold to rewrite",
        )
        assertTrue(
            denotational > literal,
            "THE SIGN, pinned: per matching operation the DENOTATIONAL reader creates more " +
                "fold-rewritable shapes than the literal one, which is the opposite of the " +
                "528,602-vs-19 production reading. The production gap is therefore not a property " +
                "of where a match leaves the [any]; it is a property of the fact population each " +
                "mode drives the engine to store.",
        )
    }

    private companion object {
        /** `L < 0`: [AnyUnrollManager] is off entirely, the pre-feature behaviour. */
        const val MANAGER_OFF = -1

        /** The frontier configuration's budget, so the second arm is the one production runs. */
        const val MANAGER_ON = 100
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

/**
 * The abstraction side of `[any]`-as-a-premise-accessor: what [TreeInitialFactAbstraction] emits for
 * a fact that carries an `[any]`, and what the `-Dopentaint.anyUnrollLimit` cap changes.
 *
 * Tree-only on purpose. The automata backend abstracts `[any]` its own way and the cactus backend
 * strips it before it arrives, so none of this is a cross-backend contract; the shared
 * `InitialFactAbstractionTest` is the wrong home for it.
 */
class AnyPremiseAbstractionTest {

    private companion object {
        val FIELD_A = FieldAccessor("A", "a", "B")
        val FIELD_B = FieldAccessor("A", "b", "B")
        val FIELD_C = FieldAccessor("B", "c", "C")

        /** The one field [UnrollStrategy] declines to unroll, so an `[any]` does not cover it. */
        val FIELD_NO_ANY = FieldAccessor("A", "<no-any>", "B")

        val MARK = TaintMarkAccessor("test-mark")
        val TYPE_A = TypeInfoAccessor("A")
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean =
            (accessor is FieldAccessor && accessor != FIELD_NO_ANY) || accessor is ElementAccessor
    }

    /**
     * The `[any]` budget now lives on the manager, keyed by `[any]` ORIGIN rather than by
     * `(entry point, access-path base)`, so a capped scenario configures the MANAGER.
     *
     * JUnit builds a fresh instance of this class per test method, so the lazy manager is per test.
     * Accessor indices are assigned per manager in first-encounter order, so facts and premises must
     * never be mixed across two of them -- hence one manager per test rather than one per limit.
     */
    private var configuredLimit: Int = -1

    /**
     * R3a ships OFF (`TreeInitialFactAbstraction.ANY_FRONTIER_PREMISE`), because a coarse `[any]`
     * premise resurrects a cleaned field. This class is the one that pins the SHAPE of that premise,
     * so it turns the arm on -- through the manager, so no global state moves and the rest of the
     * suite still sees the production default.
     */
    private var configuredFrontier: Boolean = true
    private var managerCreated = false

    private val manager: TreeApManager by lazy {
        managerCreated = true
        TreeApManager(UnrollStrategy, RefManager(), Cancellation(), configuredLimit, anyFrontierPremise = configuredFrontier)
    }

    private val base = AccessPathBase.This

    private fun abstraction(
        anyUnrollLimit: Int = -1,
        anyFrontierPremise: Boolean = true,
    ): TreeInitialFactAbstraction {
        check(!managerCreated || (anyUnrollLimit == configuredLimit && anyFrontierPremise == configuredFrontier)) {
            "the manager owns the [any] budget and the frontier arm, so both must be chosen before the first fact"
        }
        configuredLimit = anyUnrollLimit
        configuredFrontier = anyFrontierPremise
        return TreeInitialFactAbstraction(manager)
    }

    private fun premise(vararg accessors: Accessor): InitialFactAp {
        var fact = manager.mostAbstractInitialAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun fact(vararg accessors: Accessor): FinalFactAp {
        var fact = manager.createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    /** Like [fact], but left open at the leaf -- the `X.*` shape a summary exit fact carries. */
    private fun abstractFact(vararg accessors: Accessor): FinalFactAp {
        var fact = manager.mostAbstractFinalAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun TreeInitialFactAbstraction.register(fact: InitialFactAp) =
        registerNewInitialFact(fact, FactTypeChecker.Dummy)

    private fun TreeInitialFactAbstraction.add(fact: FinalFactAp) =
        addAbstractedInitialFact(fact, FactTypeChecker.Dummy)

    private fun List<Pair<InitialFactAp, FinalFactAp>>.premises(): List<InitialFactAp> = map { it.first }

    private fun List<Pair<InitialFactAp, FinalFactAp>>.assertIdentityPair(expected: InitialFactAp) {
        assertTrue(
            any { (initial, final) -> initial == expected && final.equalTo(expected) },
            "expected the identity pair ($expected, $expected.*), produced=${premises()}"
        )
    }

    /* ---------- 5A: the walk emits `[any]` as an ordinary premise accessor ---------- */

    // A base that may not unroll at all summarises every frontier it meets, which is the state a
    // capped base reaches after its budget is spent (§3.3, §7 R5). While it is still enumerating it
    // emits no `[any]` premise -- the concrete premises are strictly more precise, and the coarse
    // edge alongside them would only add false positives.
    private fun coarseAbstraction() = abstraction(anyUnrollLimit = 0)

    @Test
    fun `an any premise is emitted as an identity pair`() {
        val abstraction = coarseAbstraction()
        abstraction.register(premise().exclude(FIELD_A))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        // `this.[any]` with `this.[any].*` -- the ordinary pair, built from the same accessor chain.
        produced.assertIdentityPair(premise(AnyAccessor))
    }

    @Test
    fun `the any premise is emitted once and not again`() {
        val abstraction = coarseAbstraction()
        abstraction.register(premise().exclude(FIELD_A))

        val first = abstraction.add(fact(AnyAccessor, FIELD_C))
        assertTrue(first.premises().contains(premise(AnyAccessor)))

        // A second, deeper `[any]` fact at the same base: the premise is already in the trie.
        val second = abstraction.add(fact(AnyAccessor, FIELD_C, FIELD_C))
        assertFalse(
            second.premises().contains(premise(AnyAccessor)),
            "the emitted premise is registered in the same callback, so it can never be emitted twice"
        )
    }

    @Test
    fun `no any premise is emitted where the level carries no demand`() {
        val abstraction = coarseAbstraction()
        // A premise deeper down: it primes the root with an EMPTY exclusion set, i.e. `this` was
        // handed out and nothing has been demanded of it.
        abstraction.register(premise(FIELD_A).exclude(FIELD_C))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        assertFalse(
            produced.premises().contains(premise(AnyAccessor)),
            "with no demand at this level the fact is already covered by the `this` premise's `.*`"
        )
    }

    /* ---------- 5B: `[any]` covers field and element steps only, so marks stay visible ---------- */

    /**
     * REWRITTEN for never-unroll. This test used to assert the opposite -- that while a base was
     * still enumerating, the coarse `[any]` edge was suppressed because the concrete premises were
     * strictly more precise and the coarse one alongside them could only add false positives.
     *
     * There is no enumeration any more. R3c names the demanded accessor without materialising it and
     * R3a summarises the rest of the frontier; the two answer different callers, so both go out.
     * Design §7 R5, resolved in favour of ALWAYS.
     */
    @Test
    fun `the coarse edge and the named accessor are emitted together`() {
        val abstraction = abstraction(anyUnrollLimit = -1)
        abstraction.register(premise().exclude(FIELD_A))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        assertTrue(
            produced.premises().contains(premise(FIELD_A)),
            "R3c answers the demand for `a`; produced=${produced.premises()}"
        )
        assertTrue(
            produced.premises().contains(premise(AnyAccessor)),
            "R3a summarises the frontier the demand did not name; produced=${produced.premises()}"
        )
    }

    @Test
    fun `a mark below an any is named by the premise`() {
        // Uncapped on purpose: the walk descends an `[any]` the trie already knows about whether or
        // not the base is still unrolling.
        val abstraction = abstraction()
        // The engine refined the `[any]` premise itself: it wants the mark branch separately.
        abstraction.register(premise(AnyAccessor).exclude(MARK))

        val produced = abstraction.add(fact(AnyAccessor, MARK))

        // The walk continues PAST the `[any]`, so the mark is named: `this.[any].![m].$`.
        produced.assertIdentityPair(premise(AnyAccessor, MARK, FinalAccessor))
    }

    @Test
    fun `a mark premise registered above an any is still answered through it`() {
        val abstraction = abstraction()
        // The shape a sink precondition has: `<this>.![m].$`, sitting at `root -> mark` in the trie.
        abstraction.register(premise(MARK, FinalAccessor))

        val produced = abstraction.add(fact(AnyAccessor, MARK))

        // The fact has no mark child of its own -- the mark hangs below the `[any]` -- so this
        // premise is reachable only through the descent that takes the `[any]` zero times. It
        // matches the fact because `AccessTree.getChild` hoists a child of an `[any]` node up.
        // Losing it is what cost the earlier prototypes their `ssrf` and `path-traversal` findings.
        produced.assertIdentityPair(premise(MARK, FinalAccessor))
    }

    /* ---------- 5C: an `[any]` below an always-unroll-next accessor ---------- */

    @Test
    fun `an any below a type info accessor is emitted as an ordinary accessor`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(TYPE_A))

        // Reaches `abstractNextAccessPath`, which used to `TODO` on any `[any]` below it.
        val produced = abstraction.add(fact(TYPE_A, AnyAccessor, FIELD_C))

        produced.assertIdentityPair(premise(TYPE_A, AnyAccessor))
    }

    /* ---------- matching: which facts an `[any]` premise admits ---------- */

    @Test
    fun `delta of an any-free fact against an any premise is empty`() {
        assertTrue(
            fact(FIELD_A, FIELD_C).delta(premise(AnyAccessor)).isEmpty(),
            "an `[any]` premise is a strong precondition: only a fact that itself carries `[any]` matches"
        )
    }

    @Test
    fun `delta of an any-carrying fact is the subtree below the any`() {
        val deltas = fact(AnyAccessor, FIELD_C).delta(premise(AnyAccessor))

        assertEquals(1, deltas.size, "deltas=$deltas")
        assertFalse(deltas.single().isEmpty, "the delta is the `c` subtree that hung below the `[any]`")
        assertEquals(setOf(FIELD_C), deltas.single().getStartAccessors())
    }

    /* ---------- trace resolution: splitDelta must see through an `[any]` ---------- */

    @Test
    fun `splitDelta steps over an any in the fact and names it in the matched prefix`() {
        // The exit fact of a summary keyed on an `[any]` premise: `this.[any].*`.
        val exitFact = manager.mostAbstractFinalAp(base).prependAccessor(AnyAccessor)

        // What the sink asks the trace resolver to explain.
        val required = premise(MARK, FinalAccessor)

        val split = required.splitDelta(exitFact)

        assertEquals(1, split.size, "split=$split")
        val (matched, delta) = split.single()

        // The `[any]` is named in the matched prefix, not skipped: `MethodTraceResolver`
        // re-checks `exitFact.contains(matched)` and only an `[any]`-naming prefix passes.
        assertEquals(premise(AnyAccessor), matched)
        assertTrue(exitFact.contains(matched), "the matched prefix must be contained in the exit fact")
        assertEquals(setOf(MARK), delta.getStartAccessors())
    }

    /*
     * Past the cap the demand is answered by a summary keyed on an `[any]` PREMISE, and the exit
     * fact it carries is `X.[any].![m].*` -- the `[any]` node is not abstract, there is a mark under
     * it. Read as one literal link the premise `X.[any]` neither ends on an abstract node nor finds
     * a child to descend into, so the match failed and, with it, the whole trace: `TracePath` turns
     * a missing trace into a `TracePathGenerationResult.Failure` and `TaintAnalyzer.fullScan` drops
     * exactly those, taking the derived, registered, confirmed finding with it.
     *
     * `[any]` is zero-or-more, so all three readings below are the same premise.
     */

    @Test
    fun `splitDelta matches an any premise against the exit fact of a summary keyed on any`() {
        // The exit fact of a summary keyed on `this.[any]`: `this.[any].![m].*`, NOT abstract at the
        // `[any]` node.
        val exitFact = abstractFact(AnyAccessor, MARK)
        val required = premise(AnyAccessor)

        val split = required.splitDelta(exitFact)

        assertEquals(1, split.size, "split=$split")
        val (matched, delta) = split.single()
        assertTrue(delta.isEmpty, "`X.[any]` is `X.[any].*`, so the whole subtree is covered")
        assertTrue(
            exitFact.contains(matched),
            "MethodTraceResolver re-checks the matched prefix against the fact; matched=$matched"
        )
    }

    @Test
    fun `splitDelta reads an any premise as zero steps`() {
        val exitFact = abstractFact(MARK)
        val required = premise(AnyAccessor, MARK)

        val split = required.splitDelta(exitFact)

        assertEquals(1, split.size, "split=$split")
        val (matched, delta) = split.single()
        assertEquals(premise(MARK), matched, "the `[any]` consumed nothing, so it is not named")
        assertTrue(delta.isEmpty, "split=$split")
        assertTrue(exitFact.contains(matched))
    }

    @Test
    fun `splitDelta reads an any premise as one covered step`() {
        val exitFact = abstractFact(FIELD_A, MARK)
        val required = premise(AnyAccessor, MARK)

        val split = required.splitDelta(exitFact)

        assertEquals(1, split.size, "split=$split")
        val (matched, delta) = split.single()
        assertEquals(premise(FIELD_A, MARK), matched, "the `[any]` took the `a` step the fact has")
        assertTrue(delta.isEmpty, "split=$split")
        assertTrue(exitFact.contains(matched))
    }

    @Test
    fun `contains sees an any premise through a concrete fact`() {
        assertTrue(
            abstractFact(FIELD_A, MARK).contains(premise(AnyAccessor, MARK)),
            "`X.[any].![m]` is answered by `X.a.![m].*` -- the `[any]` takes the `a` step"
        )
        assertTrue(
            abstractFact(MARK).contains(premise(AnyAccessor, MARK)),
            "and by `X.![m].*` -- the `[any]` takes no step at all"
        )
        assertTrue(
            abstractFact(FIELD_A, FIELD_C).contains(premise(AnyAccessor)),
            "`X.[any]` is `X.[any].*`, which covers everything below X"
        )
        assertTrue(
            abstractFact(AnyAccessor, MARK).contains(premise(AnyAccessor)),
            "including the exit fact of a summary keyed on `[any]`"
        )
    }

    @Test
    fun `contains stays strict for a premise with no any`() {
        assertFalse(
            abstractFact(FIELD_A, MARK).contains(premise(MARK)),
            "an `[any]`-free premise is matched link by link, exactly as before"
        )
        assertFalse(
            abstractFact(FIELD_A).contains(premise(FIELD_B)),
            "and a fact that does not have the premise's accessor still does not contain it"
        )
    }

    @Test
    fun `splitDelta against a plain abstract fact is unchanged`() {
        val exitFact = manager.mostAbstractFinalAp(base)
        val required = premise(MARK, FinalAccessor)

        val split = required.splitDelta(exitFact)

        assertEquals(1, split.size, "split=$split")
        val (matched, delta) = split.single()
        assertEquals(premise(), matched, "no `[any]` was stepped over, so the prefix is the bare base")
        assertEquals(setOf(MARK), delta.getStartAccessors())
    }

    /* ---------- 6: the cap ---------- */

    @Test
    fun `every demanded accessor gets its own premise, with nothing materialised`() {
        val abstraction = abstraction(anyUnrollLimit = -1)
        abstraction.register(premise().exclude(FIELD_A))
        abstraction.add(fact(AnyAccessor, FIELD_C))

        val produced = abstraction.register(premise().exclude(FIELD_B))

        assertTrue(
            produced.premises().contains(premise(FIELD_B)),
            "R3c emits `this.b` straight off the demand -- `added` still holds only `this.[any].c`; " +
                "produced=${produced.premises()}"
        )
    }

    /**
     * REWRITTEN for never-unroll. This test used to assert that a spent pot stopped the second
     * accessor from being handed out. `anyUnrollLimit` gated `readChildPaidOnly`, whose only caller
     * in the engine was the unroll, so with R1 it no longer bounds the premise family at all -- it
     * decides only whether a `readChild` mint is PAID or CREDIT, i.e. whether the absorbing prepend
     * may fire. Kept, inverted, rather than deleted: the cap is still configurable, and a silent
     * change of meaning is worse than a loud one.
     */
    @Test
    fun `the any unroll limit no longer bounds the premise walk`() {
        val abstraction = abstraction(anyUnrollLimit = 1)
        abstraction.register(premise().exclude(FIELD_A))

        val first = abstraction.add(fact(AnyAccessor, FIELD_C))
        first.assertIdentityPair(premise(AnyAccessor))
        assertTrue(
            first.premises().contains(premise(FIELD_A)),
            "produced=${first.premises()}"
        )

        val second = abstraction.register(premise().exclude(FIELD_B))
        assertTrue(
            second.premises().contains(premise(FIELD_B)),
            "nothing was spent, because nothing was unrolled; produced=${second.premises()}"
        )
    }

    @Test
    fun `an accessor demanded and then supplied is not emitted twice`() {
        val abstraction = abstraction(anyUnrollLimit = 1)
        abstraction.register(premise().exclude(FIELD_A))
        abstraction.add(fact(AnyAccessor, FIELD_C))
        val demanded = abstraction.register(premise().exclude(FIELD_B))
        assertTrue(
            demanded.premises().contains(premise(FIELD_B)),
            "R3c hands it out before any fact supplies it; produced=${demanded.premises()}"
        )

        // The caller really does send taint at `this.b` now. `root.child(b)` exists, so R2 takes the
        // descend arm: the self-registration at the emission site is the only de-duplication there
        // is, and it keys on the PREMISE rather than on the demand.
        val supplied = abstraction.add(fact(FIELD_B, FIELD_C))

        assertFalse(
            supplied.premises().contains(premise(FIELD_B)),
            "already handed out; produced=${supplied.premises()}"
        )
    }

    /* ---------- 7: never unroll -- the rules that replace it ---------- */

    /**
     * The production default. R3a is off, so the demand is answered by R3c alone -- precisely, and
     * without the coarse edge whose entry fact cannot carry a node deletion.
     */
    @Test
    fun `by default the frontier is answered precisely and no any premise is emitted`() {
        val abstraction = abstraction(anyFrontierPremise = false)
        abstraction.register(premise().exclude(FIELD_A))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        produced.assertIdentityPair(premise(FIELD_A))
        assertFalse(
            produced.premises().contains(premise(AnyAccessor)),
            "the coarse edge only adds false positives while R3c is still answering; " +
                "produced=${produced.premises()}"
        )
    }

    /**
     * R3b. `[any]` is zero-or-more steps over FIELD and ELEMENT, so a taint mark below one is not
     * something `p.[any]` denotes -- and the mark is the finding. The demand sits at `p`, and the
     * premise that answers it is `p.![m]`: `AccessTree.getChild` hoists the `[any]`'s child up, so
     * the `[any]`-free premise matches the `[any]`-carrying fact that produced it.
     *
     * The `[any]`-CARRYING member of the family, `p.[any].![m]`, is deliberately not emitted here.
     * Naming it speculatively off demand registered at `p` is what resurrected the cleaned field in
     * `TreeCleanerFieldSensitivityAnalysisTest`: an entry fact `p.[any].![m].*` cannot express a
     * node deletion inside the `[any]`. It is still reachable where the engine has actually refined
     * `p.[any]` itself -- `a mark below an any is named by the premise`, above, is that case.
     */
    @Test
    fun `a demanded mark below an any is named at this prefix`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(MARK))

        val produced = abstraction.add(fact(AnyAccessor, MARK))

        assertTrue(
            produced.premises().contains(premise(MARK, FinalAccessor)),
            "the `[any]` taken zero times; produced=${produced.premises()}"
        )
        assertFalse(
            produced.premises().contains(premise(AnyAccessor, MARK, FinalAccessor)),
            "not speculatively, off demand registered one level above; produced=${produced.premises()}"
        )
    }

    /**
     * R3c: the accessor is named although it exists in NO concrete branch of the fact, and nothing
     * is written into `added`. This is what the automata backend has always done
     * (`AutomataInitialFactAbstraction.abstractGraph`), and eight scenarios of the cross-backend
     * `InitialFactAbstractionTest` assert it.
     */
    @Test
    fun `a demanded accessor absent from the fact is named without being materialised`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(FIELD_A))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        produced.assertIdentityPair(premise(FIELD_A))

        // Nothing was materialised: a second, unrelated demand still sees the same `[any]` frontier
        // rather than a `this.a.[any].*` copy of it.
        val second = abstraction.register(premise().exclude(FIELD_B))
        second.assertIdentityPair(premise(FIELD_B))
    }

    /**
     * R4. Emitting `this.a` registers the trie node but materialises nothing, so without the virtual
     * descent the abstraction would stick one level below every `[any]` forever. `getChild`
     * synthesises the node the unroll used to copy, and the walk descends into it.
     */
    @Test
    fun `the ladder climbs through a synthesised node`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(FIELD_A))
        abstraction.add(fact(AnyAccessor, FIELD_C))

        val second = abstraction.register(premise(FIELD_A).exclude(FIELD_C))

        assertTrue(
            second.premises().contains(premise(FIELD_A, FIELD_C)),
            "the `[any]` re-installed below the synthesised `a` still answers demand; " +
                "produced=${second.premises()}"
        )
    }

    /**
     * The invariant that makes rules 2 and 3 compose: emitting `p.[any]` answers the demand at that
     * level FOR NOW, and must not retire it.
     *
     * `FIELD_NO_ANY` is the accessor this test needs: the strategy declines to unroll it, so it is
     * NOT covered by the `[any]` and R3c cannot answer it eagerly. The coarse edge goes out, the
     * `{<no-any>}` demand stays on the books, and when supply catches up R2 fires on the new fact
     * exactly as if the `[any]` premise had never been emitted.
     */
    @Test
    fun `the coarse any premise does not consume the demand`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(FIELD_NO_ANY))

        val coarse = abstraction.add(fact(AnyAccessor, FIELD_C))
        assertTrue(
            coarse.premises().contains(premise(AnyAccessor)),
            "produced=${coarse.premises()}"
        )
        assertFalse(
            coarse.premises().contains(premise(FIELD_NO_ANY)),
            "the `[any]` does not cover it, so there is no evidence for it yet; produced=${coarse.premises()}"
        )

        val supplied = abstraction.add(fact(FIELD_NO_ANY, FIELD_C))

        assertTrue(
            supplied.premises().contains(premise(FIELD_NO_ANY)),
            "the demand was never marked answered; produced=${supplied.premises()}"
        )
    }

    /**
     * Bases are independent, and stay so. Each holds its own `added` accumulator and its own demand
     * trie, so a premise handed out at one says nothing about what the other has been asked.
     */
    @Test
    fun `a second base gets its own premises`() {
        val abstraction = abstraction(anyUnrollLimit = 1)

        abstraction.register(premise().exclude(FIELD_A))
        abstraction.add(fact(AnyAccessor, FIELD_C))
        abstraction.register(premise().exclude(FIELD_B))

        val otherBase = AccessPathBase.Argument(0)
        abstraction.register(manager.mostAbstractInitialAp(otherBase).exclude(FIELD_A))

        val otherFact = manager.createFinalAp(otherBase, ExclusionSet.Empty)
            .prependAccessor(FIELD_C)
            .prependAccessor(AnyAccessor)
        val produced = abstraction.add(otherFact)

        val expected = manager.mostAbstractInitialAp(otherBase).prependAccessor(FIELD_A)
        assertTrue(
            produced.premises().contains(expected),
            "a fresh origin has its own full pot; produced=${produced.premises()}"
        )
    }
}

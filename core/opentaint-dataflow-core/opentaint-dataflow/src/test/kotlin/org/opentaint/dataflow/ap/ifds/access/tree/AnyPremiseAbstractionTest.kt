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
import kotlin.test.assertNotNull
import kotlin.test.assertNull
import kotlin.test.assertTrue

/**
 * The abstraction side of `[any]`-as-a-premise-accessor: what [TreeInitialFactAbstraction] emits for
 * a fact that carries an `[any]`.
 *
 * ## The rule these tests pin
 *
 * Design: `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`. **A fact's premises are
 * its literal prefixes.** `a.f.[any].*` yields at most `a`, `a.f`, `a.f.[any]` -- three, not
 * `sum n!/(n-k)!`. Nothing anywhere synthesises a concrete accessor out of an `[any]` in order to
 * MATCH a premise, and `[TreeApManager.literalAnyMatch]` (default true) is the flag that says so.
 *
 * Two rules of the walk were deleted to get there, and most of the rewrites in this file are the
 * inversion of a test that used to assert one of them:
 *
 *  - **R3c** emitted a concrete `p.a` for an accessor demanded at this level, covered by the
 *    `[any]`, and held literally nowhere in the fact.
 *  - **R4** then descended into it, reading `added.getChild(a)` -- whose third term SYNTHESISED `a`
 *    out of the `[any]` edge -- so the next level did the same thing one link lower.
 *
 * The two were one loop: R3c handed out the premise and the synthesis term matched it straight back
 * against the same `[any]`, consuming a premise link without descending the fact. What survives --
 * R0, R2, R3a, R3b -- emits only literal prefixes, and R3a's coarse `p.[any]`, whose paired entry
 * fact `p.[any].*` subsumes every `p.a.*` R3c used to ask for, is what answers the demand instead
 * (design §2.3, §2.5). It is strictly coarser, so the risk is false positives, never a lost flow.
 *
 * Tree-only on purpose. The automata backend abstracts `[any]` its own way -- it still names the
 * absent accessor, and `InitialFactAbstractionTest` forks on exactly that (design §4) -- and the
 * cactus backend strips it before it arrives, so none of this is a cross-backend contract.
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
    private var managerCreated = false

    private val manager: TreeApManager by lazy {
        managerCreated = true
        TreeApManager(UnrollStrategy, RefManager(), Cancellation(), configuredLimit)
    }

    private val base = AccessPathBase.This

    private fun abstraction(anyUnrollLimit: Int = -1): TreeInitialFactAbstraction {
        check(!managerCreated || anyUnrollLimit == configuredLimit) {
            "the manager owns the [any] budget, so the limit must be chosen before the first fact is built"
        }
        configuredLimit = anyUnrollLimit
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

    /**
     * The other half of every literal-rule assertion in this file. A premise that is NOT handed out
     * is the whole content of the change, so it is asserted explicitly rather than left to an
     * exact-set comparison that a future emission could quietly widen.
     */
    private fun List<Pair<InitialFactAp, FinalFactAp>>.assertNotEmitted(unexpected: InitialFactAp, why: String) {
        assertFalse(premises().contains(unexpected), "$why; produced=${premises()}")
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
     * The coarse edge, and nothing beside it.
     *
     * This test has been through three regimes and the name has followed the rule each time. It
     * began as "the coarse edge is SUPPRESSED": while a base was still enumerating, the concrete
     * premises the unroll produced were strictly more precise and a coarse edge alongside them could
     * only add false positives. Never-unroll made it "both go out" -- R3c named the demanded
     * accessor, R3a summarised the rest of the frontier. The literal rule
     * (`docs/superpowers/specs/2026-08-27-literal-any-matching-design.md` §2.3) deletes R3c, so
     * only the second half is left: the coarse edge is not one answer among several, it is the
     * answer, and the level's entire output is one pair.
     *
     * Both absences matter and both are asserted. `a` is the accessor the deleted rule named off the
     * demand; `c` is the accessor the fact actually holds, but holds BELOW the `[any]`, so it is not
     * a literal prefix from the root either and R3b skips it as covered.
     */
    @Test
    fun `the coarse edge goes out alone`() {
        val abstraction = abstraction(anyUnrollLimit = -1)
        abstraction.register(premise().exclude(FIELD_A))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        assertTrue(
            produced.premises().contains(premise(AnyAccessor)),
            "R3a summarises the whole frontier; produced=${produced.premises()}"
        )
        assertEquals(
            1, produced.size,
            "the coarse edge is the level's entire output; produced=${produced.premises()}"
        )
        produced.assertNotEmitted(
            premise(FIELD_A),
            "R3c is deleted: a demand does not buy an accessor the fact holds literally nowhere"
        )
        produced.assertNotEmitted(
            premise(FIELD_C),
            "`c` hangs below the `[any]`, so it is not a literal prefix of the fact either"
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

    /* ---------- 6: the literal rule -- what a demand no longer buys ---------- */

    /**
     * The COUNT, rather than the shape.
     *
     * Under R3c every demanded accessor bought a premise of its own, so a level carrying `k` demands
     * handed out `k` concrete premises and each of them re-armed the level below -- the
     * `sum n!/(n-k)!` family `AnyUnrollGrowthPatternTest` measures. The literal rule
     * (`docs/superpowers/specs/2026-08-27-literal-any-matching-design.md` §2.3) caps the level at the
     * fact's own literal edges, and there is exactly one of those here. So the second demand buys
     * nothing at all: `<this>.[any]` is already out, its entry fact `<this>.[any].*` subsumes
     * `<this>.b.*` as it subsumed `<this>.a.*`, and no rule left in the walk turns a demand into an
     * accessor the fact does not hold.
     */
    @Test
    fun `a second demanded accessor gets no premise of its own`() {
        val abstraction = abstraction(anyUnrollLimit = -1)
        abstraction.register(premise().exclude(FIELD_A))

        val first = abstraction.add(fact(AnyAccessor, FIELD_C))
        assertEquals(
            listOf(premise(AnyAccessor)), first.premises(),
            "one literal edge, one premise"
        )

        val produced = abstraction.register(premise().exclude(FIELD_B))

        produced.assertNotEmitted(
            premise(FIELD_B),
            "R3c would have emitted `<this>.b` straight off the demand -- `added` holds only `<this>.[any].c`"
        )
        assertEquals(
            emptyList<InitialFactAp>(), produced.premises(),
            "and the coarse edge that already answers `a` answers `b` too, so the level stays at one premise"
        )
    }

    /**
     * The invariant itself, observed: `|premises(F)| <= |nodes(F)|`, and the premises ARE the literal
     * prefixes (`docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`, the headline).
     *
     * This test has also been through three regimes, and it is the one where the walk was left
     * genuinely unbounded in between. It began as "a spent pot stops the second accessor being handed
     * out". Never-unroll made it "the pot no longer bounds anything" -- true, because `anyUnrollLimit`
     * gated `readChildPaidOnly`, whose only engine caller was the unroll -- and correct as far as it
     * went, but it left R3c/R4 climbing one rung per round with nothing to stop them. The literal rule
     * supplies the bound the pot never was, and it is structural rather than budgeted: the fact
     * `<this>.a.[any].c` has three non-root nodes, so three premises exist and a fourth refinement
     * produces none.
     *
     * Emit, refine, emit again -- and then stop. `anyUnrollLimit = 1` stays pinned to show the bound
     * does not come from the pot: a budget of one would have permitted a second rung, and there is no
     * second rung to permit.
     */
    @Test
    fun `the premise set is bounded by the fact's literal prefixes`() {
        val abstraction = abstraction(anyUnrollLimit = 1)
        abstraction.register(premise().exclude(FIELD_A))

        // Emit. `a` is the one accessor the fact holds literally at the root, so R2 hands it out.
        val emitted = abstraction.add(fact(FIELD_A, AnyAccessor, FIELD_C))
        assertEquals(listOf(premise(FIELD_A)), emitted.premises(), "produced=${emitted.premises()}")

        // Refine at `<this>.a`, emit again: the next literal prefix is the `[any]` edge itself.
        val refinedAtA = abstraction.register(premise(FIELD_A).exclude(FIELD_C))
        assertEquals(
            listOf(premise(FIELD_A, AnyAccessor)), refinedAtA.premises(),
            "produced=${refinedAtA.premises()}"
        )
        refinedAtA.assertNotEmitted(
            premise(FIELD_A, FIELD_C),
            "the rung R3c used to add here, synthesising `c` out of the `[any]` it never stepped over"
        )

        // Refine at `<this>.a.[any]`: `c` IS held literally below the `[any]`, so it is a prefix.
        val refinedAtAny = abstraction.register(premise(FIELD_A, AnyAccessor).exclude(FIELD_C))
        assertEquals(
            listOf(premise(FIELD_A, AnyAccessor, FIELD_C)), refinedAtAny.premises(),
            "produced=${refinedAtAny.premises()}"
        )

        // The fact is out of literal prefixes. Under R3c/R4 this is where the ladder went on for
        // ever, one link longer per round; now it stops.
        val exhausted = abstraction.register(premise(FIELD_A, AnyAccessor, FIELD_C).exclude(FIELD_B))
        assertEquals(
            emptyList<InitialFactAp>(), exhausted.premises(),
            "produced=${exhausted.premises()}"
        )

        val all = emitted.premises() + refinedAtA.premises() + refinedAtAny.premises() + exhausted.premises()
        assertEquals(
            listOf(
                premise(FIELD_A),
                premise(FIELD_A, AnyAccessor),
                premise(FIELD_A, AnyAccessor, FIELD_C),
            ),
            all,
            "the whole run yields the fact's literal prefixes, one per node, and nothing else"
        )
    }

    /**
     * Demand alone no longer buys a premise; SUPPLY does, and only once.
     *
     * The first half of this test used to assert that R3c handed `<this>.b` out on the demand, before
     * any fact held `b`. The literal rule inverts that half and leaves the second half exactly as it
     * was: R2's emit arm is untouched, so the moment a fact holds `b` as an edge of its own the
     * premise goes out -- and the self-registration at the emission site is still the only
     * de-duplication there is, keyed on the PREMISE rather than on the demand.
     *
     * So the ordering the old rule erased is visible again: a demand for `b` against a fact that
     * reaches `b` only through its `[any]` is answered coarsely, and the concrete premise waits for
     * a fact that actually carries it.
     */
    @Test
    fun `an accessor is emitted when the fact supplies it literally and only then`() {
        val abstraction = abstraction(anyUnrollLimit = 1)
        abstraction.register(premise().exclude(FIELD_B))

        val underAny = abstraction.add(fact(AnyAccessor, FIELD_C))
        underAny.assertIdentityPair(premise(AnyAccessor))
        underAny.assertNotEmitted(
            premise(FIELD_B),
            "the fact reaches `b` only through its `[any]`, so `b` is not one of its literal prefixes"
        )

        // The caller really does send taint at `this.b` now, so `b` is an edge of the fact and R2
        // emits it -- the demand was never marked answered by the coarse edge.
        val supplied = abstraction.add(fact(FIELD_B, FIELD_C))
        assertTrue(
            supplied.premises().contains(premise(FIELD_B)),
            "supply is what R2 waits for; produced=${supplied.premises()}"
        )

        // And exactly once: the emission registered `root.child(b)`, so the next `b`-carrying fact
        // takes R2's descend arm instead.
        val again = abstraction.add(fact(FIELD_B, FIELD_C, FIELD_C))
        again.assertNotEmitted(premise(FIELD_B), "already handed out")
    }

    /* ---------- 7: the rules that survive, and the two that do not ---------- */

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
     * The literal rule at the point where it bites: R3c's exact firing condition, inverted.
     *
     * `a` is demanded at this level, the `[any]` covers it, and no branch of the fact holds it -- so
     * R3c named `<this>.a` here, materialising nothing, which is what the automata backend still
     * does (`AutomataInitialFactAbstraction.abstractGraph`). The tree backend no longer does
     * (`docs/superpowers/specs/2026-08-27-literal-any-matching-design.md` §2.3), because the concrete
     * premise was the emitting half of a ratchet: the matching reader synthesised `a` straight back
     * out of the same `[any]`, consuming a premise link without descending the fact, and R4 then
     * descended so the level below repeated it one link longer. The cross-backend
     * `InitialFactAbstractionTest` forks on this rather than agreeing (design §4).
     *
     * What answers the demand is R3a's coarse `<this>.[any]`, which was already going out at this
     * level. Coarser, not blind, and the last two assertions are the difference: the entry fact the
     * coarse premise carries still reads THROUGH the demanded `a` step, because `readAccessor` is a
     * denotation channel and the literal rule touches only the matching channels (design §2). The
     * callee's result under `<this>.[any].*` therefore subsumes its result under `<this>.a.*`; what
     * is given up is precision, not reachability.
     */
    @Test
    fun `a demanded accessor absent from the fact is answered by the coarse any edge`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(FIELD_A))

        val produced = abstraction.add(fact(AnyAccessor, FIELD_C))

        produced.assertIdentityPair(premise(AnyAccessor))
        produced.assertNotEmitted(
            premise(FIELD_A),
            "R3c is deleted: nothing synthesises `a` out of the `[any]` to name it"
        )

        val entryFact = produced.single().second
        assertNotNull(
            entryFact.readAccessor(FIELD_A),
            "the coarse premise's entry fact still denotes the demanded field step: entry=$entryFact"
        )
        assertNull(
            entryFact.readAccessor(FIELD_NO_ANY),
            "and only the steps the `[any]` covers -- the coarsening is bounded: entry=$entryFact"
        )
    }

    /**
     * R4, deleted with R3c -- the two only ever made sense as a pair
     * (`docs/superpowers/specs/2026-08-27-literal-any-matching-design.md` §2.3).
     *
     * R4 was the unique descent in this walk that entered a state the fact does not hold literally.
     * Emitting `<this>.a` registered the trie node but materialised nothing, so R4 read
     * `added.getChild(a)` -- whose third term SYNTHESISES `a` out of the `[any]` edge, re-installing
     * the `[any]` below it -- and the walk descended there, where R3c handed out `<this>.a.c`, and so
     * on for ever. That is why the growth pattern survived the removal of the unroll: never-unroll
     * took away the fact materialisation, not the premise enumeration.
     *
     * With both gone the walk cannot be routed into `a` at all, and this test asserts the negative
     * directly: the demand is registered AT `<this>.a`, the fact still carries its `[any]`, the trie
     * node is live -- and nothing comes out, because the fact has no literal `a` edge to descend.
     */
    @Test
    fun `the ladder does not climb into a node the fact reaches only through its any`() {
        val abstraction = abstraction()
        abstraction.register(premise().exclude(FIELD_A))

        val first = abstraction.add(fact(AnyAccessor, FIELD_C))
        first.assertIdentityPair(premise(AnyAccessor))

        // The rung R4 used to climb to: demand registered one link below, on the accessor the fact
        // reaches only through its `[any]`.
        val second = abstraction.register(premise(FIELD_A).exclude(FIELD_C))

        second.assertNotEmitted(
            premise(FIELD_A, FIELD_C),
            "the rung the R3c/R4 pair used to hand out, `[any]` re-installed below a synthesised `a`"
        )
        assertEquals(
            emptyList<InitialFactAp>(), second.premises(),
            "and no other rung either: the walk never reaches the trie node at all; " +
                "produced=${second.premises()}"
        )
    }

    /**
     * The invariant that makes rules 2 and 3 compose: emitting `p.[any]` answers the demand at that
     * level FOR NOW, and must not retire it.
     *
     * `FIELD_NO_ANY` is the accessor this test was built around: the strategy declines to unroll it,
     * so the `[any]` does not cover it and R3c could not answer it eagerly even when R3c existed.
     * Under the literal rule no accessor is answered eagerly, so the test now pins the general case
     * rather than a carve-out -- but the uncovered accessor keeps it honest, because for a COVERED
     * one the coarse edge's `.*` would make the second emission indistinguishable from subsumption.
     *
     * The coarse edge goes out, the `{<no-any>}` demand stays on the books, and when supply catches
     * up R2 fires on the new fact exactly as if the `[any]` premise had never been emitted.
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
     *
     * Under the literal rule that independence shows in the COARSE edge rather than in a concrete
     * one, which is what makes it worth re-asserting: `<this>` has already spent its `[any]` premise
     * -- a deeper `[any]` fact there adds nothing -- while `arg(0)`, asked the same question, still
     * has its own to hand out. And the rule holds at every base: `arg(0).a` is no more emitted than
     * `<this>.a` was.
     */
    @Test
    fun `a second base gets its own premises`() {
        val abstraction = abstraction(anyUnrollLimit = 1)

        abstraction.register(premise().exclude(FIELD_A))
        abstraction.add(fact(AnyAccessor, FIELD_C)).assertIdentityPair(premise(AnyAccessor))
        abstraction.register(premise().exclude(FIELD_B))

        // Spent at `<this>`: the coarse premise is in the trie, so the walk descends past it.
        val spent = abstraction.add(fact(AnyAccessor, FIELD_C, FIELD_C))
        assertEquals(
            emptyList<InitialFactAp>(), spent.premises(),
            "produced=${spent.premises()}"
        )

        val otherBase = AccessPathBase.Argument(0)
        abstraction.register(manager.mostAbstractInitialAp(otherBase).exclude(FIELD_A))

        val otherFact = manager.createFinalAp(otherBase, ExclusionSet.Empty)
            .prependAccessor(FIELD_C)
            .prependAccessor(AnyAccessor)
        val produced = abstraction.add(otherFact)

        val otherCoarse = manager.mostAbstractInitialAp(otherBase).prependAccessor(AnyAccessor)
        val otherConcrete = manager.mostAbstractInitialAp(otherBase).prependAccessor(FIELD_A)

        assertEquals(
            listOf(otherCoarse), produced.premises(),
            "a fresh base has its own demand trie, so its coarse edge is still to come"
        )
        produced.assertNotEmitted(
            otherConcrete,
            "and the literal rule holds at every base: R3c is deleted, not merely spent at `<this>`"
        )
    }
}

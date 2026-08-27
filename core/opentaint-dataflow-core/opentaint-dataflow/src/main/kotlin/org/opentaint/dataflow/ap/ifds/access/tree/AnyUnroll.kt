package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.util.ConcurrentReadSafeInt2ObjectMap
import org.opentaint.dataflow.util.forEachEntry
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong

/**
 * How a state was obtained, which is what the prepend keys on instead of the pot.
 *
 * `budgetExhausted` is a property of the POT, shared by every `[any]` position descended from one
 * origin, so once it fires every covered accessor prepended above any `[any]` of that origin is
 * dropped -- including ones the callee genuinely produced. Given a fact `x.[any]`, a premise
 * `arg0.a.*` and a conclusion `ret.b.*`, `b` is not a step out of the caller's `[any]`: the callee
 * wrote field `b` of the return value. Dropping it turns `ret.b.X` into `ret.[any].X`, which then
 * activates every premise rooted at `ret` -- and coarsening a fact INCREASES the premises it matches.
 *
 * The automaton can draw the distinction the pot cannot: `a` is a transition out of the state the
 * fact's `[any]` carries and `b` is not. Written once at the mint; a union is the only other writer.
 *
 * The three values are ordered writable-to-absorbing, which is what makes the `min`/`max` of
 * [AnyUnrollKindMerge] mean what it says. There is no fourth: the read never stops recording, so
 * there is no tier past `CREDIT` to reach.
 */
enum class AnyUnrollKind {
    /**
     * A start state. NEUTRAL in the merge and writable.
     *
     * Origins are minted constantly and 11,482 of 11,625 thingsboard unions are cross-dag fusions,
     * each merging two start states. If origins carried `PAID`, `PreferBelow` would demote every
     * `CREDIT` class on its first fusion with any fresh origin, irreversibly -- and the pot is
     * untouched by a fusion, so `budgetExhausted` would say SPENT while the kind said WRITABLE and
     * the absorption would never fire at all. Lowering `L` would not help: an origin is `PAID` at
     * every `L`, including 0. `PreferBeyond` mirrors it, spreading `CREDIT` by contagion until every
     * `[any]` in the program is absorption-eligible. Neither outcome is a knob working; both are the
     * fusion rate deciding for it. A start state was never bought and has no opinion.
     */
    ORIGIN,

    /** Minted while `dag.total < L`: the pot paid for it, so a step above it is still real structure. */
    PAID,

    /** Minted after the pot was spent. Absorption-eligible -- but only for accessors it recorded. */
    CREDIT,
}

/**
 * What kind the survivor of a union carries. `-Dopentaint.anyUnrollKindMerge=below|beyond`.
 *
 * A precision knob, never a soundness one: absorption is correct at any state, so this decides only
 * WHICH superset is produced.
 *
 * `PreferBelow` is the meet -- only states that went on credit absorb -- so the decision over time is
 * only ever finer and a re-derivation is a SUBSET of what is stored, which for a closed fact the
 * merge guard absorbs outright. `PreferBeyond` is the join: storage changes in both shapes and the
 * fact re-enters the worklist carrying an `[any]` matching strictly more premises.
 *
 * `PreferBeyond` cannot fail to terminate, and saying so precisely is what makes it an experiment
 * rather than a fear: under a FIXED strategy the kind is monotone in one direction over a
 * three-element lattice, so each state changes kind at most twice and each change re-derives a
 * bounded fact population. The strategy must therefore be fixed for the run.
 */
enum class AnyUnrollKindMerge { PreferBelow, PreferBeyond }

/**
 * What `L` is a budget FOR: one pot per origin-component, or one pot for the whole run.
 *
 * [PerDag] is the shipped rule and the one the design argues for -- a population bound per `[any]`
 * origin. It has a measured consequence that the design did not anticipate: on conductor the run
 * creates 141 origin-components and **one** of them ever reaches `L`, because the components are
 * tiny (mean 2.3 states) while the automaton in aggregate is not. The effective budget is therefore
 * `141 x L`, and almost every state is stamped `PAID` for good.
 *
 * [Global] changes only which counter the mint compares against, so the difference between the two
 * arms is exactly the unit of the bound and nothing else. It is an EXPERIMENT, not a
 * recommendation: `budgetExhausted`, which governs the initial-fact abstraction's unroll, stays on
 * the per-dag rule under both, so the arms differ in kind assignment alone.
 *
 * `-Dopentaint.anyUnrollKindPolicy=perDag|global`.
 */
enum class AnyUnrollKindPolicy { PerDag, Global, AlwaysCredit, Rescore }

/**
 * The order [AnyUnrollKindPolicy.Rescore] spends its budget in.
 *
 * [Bfs] keeps the states nearest the origin `PAID`. It is the obvious reading of "keep a bounded
 * prefix precise", and on conductor it is the wrong one: the shallow states are the ones the whole
 * fact population sits at, so breadth-first spends the entire budget protecting exactly the state
 * that costs the most. Measured: one state governed 6,544 of the 6,570 `[any]` positions in a
 * 40,262-node fact and declined 46% of every prepend in the run, and the re-score kept it `PAID`.
 *
 * [Population] spends the budget on the states that gate the LEAST traffic, so the heavily-trafficked
 * ones are demoted to `CREDIT` and become eligible to absorb. Precision is kept where it is cheap.
 * The weight is [AnyUnrollState.traffic]; see its doc for why an approximate count is enough.
 *
 * `-Dopentaint.anyUnrollRescoreStrategy=bfs|population`.
 */
enum class AnyUnrollRescoreStrategy { Bfs, Population }

/**
 * The budget pot shared by every `[any]` position descended from one origin.
 *
 * One dag per `[any]` ORIGIN -- the point where an `[any]` edge was created with no predecessor to
 * inherit from. Every state reachable from that origin spends [total] from here, which is what makes
 * the bound a POPULATION bound rather than a per-derivation one: a budget that forks with the
 * derivation bounds the length of each chain while letting the number of chains grow like
 * `breadth^L`.
 *
 * Dags are themselves union-find nodes ([parent]): when two automata have to be fused their pots
 * combine. [rootState] is the only thing the dag has to retain about its automaton, and it exists
 * solely so a fusion can reach the two start states to merge them.
 */
class AnyUnrollDag(@JvmField val id: Int) {
    /** DSU link; `null` means this dag is a representative. Written only under the manager lock. */
    @Volatile
    @JvmField
    var parent: AnyUnrollDag? = null

    /**
     * The pot: how much of this origin's budget has been spent.
     *
     * The unit is set by [AnyUnrollManager.pathLengthCost] -- by default the SUM OF THE LENGTHS of
     * the accessor sequences materialised out of this origin, so `L` bounds accessors rather than
     * words. See [AnyUnrollManager.DEFAULT_PATH_LENGTH_COST].
     *
     * Monotone: it is an accumulator over mint EVENTS. Transitions are added and never removed, and
     * a state merge -- which genuinely destroys states -- moves nothing here. That is deliberate and
     * it is what a recomputed measure could not offer: folding a chain into a self-loop lowers the
     * sum of path lengths OVER THE CURRENT STRUCTURE, and a budget a program loop can refund never
     * terminates.
     */
    @JvmField
    var total: Int = 0

    /** Diagnostics only: reads this pot refused after it was spent. Written under the manager lock. */
    @JvmField
    var refusals: Int = 0

    /**
     * Whether this pot has already been counted as exhausted, so the progress line counts a
     * TRANSITION rather than a state.
     *
     * [total] is monotone and this latch is never cleared, so the reported figure only ever drifts
     * downward at a fusion -- where the decrement is exactly the dag that ceased to exist. Written
     * under the manager lock, beside [total].
     */
    @JvmField
    var exhaustedCounted: Boolean = false

    /**
     * How many live states this pot's automaton holds.
     *
     * Maintained incrementally at the mint, at the fusion and at each productive state merge --
     * never by traversal, for the reason [AnyUnrollState] gives: the automaton is allowed to be
     * cyclic. It exists so `maxStatesPerDag` can be reported without a registry.
     */
    @JvmField
    var states: Int = 0

    /**
     * The next `total` at which [AnyUnrollKindPolicy.Rescore] re-assigns this dag's kinds.
     *
     * Doubling rather than "every time it grows", so a dag is re-scored O(log total) times. The kind
     * lattice's termination argument assumes a bounded number of kind changes per state; a re-score
     * that fired on every mint would not have one.
     */
    @JvmField
    var nextRescoreAt: Int = Int.MAX_VALUE

    /**
     * The automaton's start state, needed only to fuse two automata into one.
     *
     * Closes a reference cycle (dag -> root state -> dag) that the collector handles without help.
     */
    @JvmField
    var rootState: AnyUnrollState? = null

    override fun toString(): String = "dag#$id(total=$total)"
}

/**
 * One position in the deterministic automaton of concrete accessor sequences materialised out of an
 * `[any]`.
 *
 * The structure is NOT a trie and not even a DAG -- it must be allowed to become cyclic. A program
 * loop `while (*) { x = x.a }` over a fact `x.[any].*` produces `union(m, m.a)`, which writes
 * `m --a--> m`; that self-loop is exactly how the loop reaches its fixed point, because the next read
 * of `a` at `m` finds an existing transition, mints nothing and charges nothing. Refusing to create
 * it would produce a fresh state every lap and the analysis would never converge.
 *
 * Consequently NOTHING may compute a quantity by traversing the automaton: on a cycle the accepted
 * language is infinite. [pathCount] is maintained incrementally at the point of change instead.
 */
class AnyUnrollState(
    /** Dense, from an [AtomicInteger]; used for hashing only, never for identity or lookup. */
    @JvmField val id: Int,
    /** Strong reference to the pot this state spends from. */
    @JvmField val dag: AnyUnrollDag,
) {
    /**
     * DSU link; `null` means this state is a representative.
     *
     * Written by [AnyUnrollManager.union] (which only ever writes to a root, under the lock) and by
     * [find]'s path halving (which only ever writes to a non-root whose parent is also a non-root).
     * The two write sets are disjoint, which is what lets halving stay lock-free with a plain
     * volatile write and no CAS.
     */
    @Volatile
    @JvmField
    var parent: AnyUnrollState? = null

    /**
     * How many distinct accessor sequences reach this state.
     *
     * A state can be reached by more than one sequence -- that is what a union does, and it is the
     * whole reason the structure is an automaton rather than a trie. Charging 1 for a new transition
     * out of a shared state would under-report the population by the sharing factor, compounding
     * with every merge, so the charge is proportional to `pathCount` rather than flat -- see
     * [lengthSum] and [AnyUnrollManager.readChild].
     *
     * Maintained incrementally and saturating; never recomputed by traversal.
     */
    @JvmField
    var pathCount: Int = 1

    /**
     * The sum of the LENGTHS of the sequences that reach this state: `SUM |w|` over those `w`.
     *
     * [pathCount] counts the WORDS an `[any]` has sold at this position; this counts their LETTERS.
     * They are different measures of the same population and the pot charges whichever
     * [AnyUnrollManager.pathLengthCost] selects, because a word is not a unit of cost -- a state
     * reached by one sequence of length 40 has materialised forty accessors, and the word-count
     * measure bills it the same 1 as a state one step from the origin.
     *
     * Maintained by the SAME incremental discipline as [pathCount], for the same reason: the
     * automaton is allowed to be cyclic, so no quantity here may ever be recomputed by traversing it.
     * Extending every word reaching `current` by one accessor produces `pathCount` new words whose
     * lengths total `lengthSum + pathCount`, which is the whole of the update rule.
     *
     * A cycle contributes at most ONE lap. The transition that closes it was minted -- and charged --
     * as a fresh state before [mergeStates] folded that state into an ancestor; every later lap finds
     * the transition already there, mints nothing and charges nothing. So the measure this maintains
     * is "sum of path lengths over paths that traverse each cycle zero or one times", which is finite
     * where the accepted language is not.
     */
    @JvmField
    var lengthSum: Int = 0

    /**
     * How this state was obtained -- see [AnyUnrollKind].
     *
     * Mutable after construction, and deliberately OUTSIDE node identity: `AccessNode.hash` mixes
     * only [id], which is immutable. A hash that moved under a live entry is the central hazard here
     * -- the interner's buckets, the edge sets and the enqueued-unchanged set would each silently
     * lose an entry the moment a union changed a kind.
     *
     * The corollary is that a kind change RE-PROPAGATES NOTHING: the merge guard returns the
     * receiver, every storage `===` fires, stored facts are untouched. A coarsening or a refinement
     * takes effect only for facts built after it.
     */
    @JvmField
    var kind: AnyUnrollKind = AnyUnrollKind.ORIGIN

    /**
     * Diagnostics only: minted by `readChildPaidOnly`, the initial-fact abstraction's unroll.
     *
     * That entry point passes `paid = true` unconditionally and has no CREDIT branch at all -- past
     * the limit it REFUSES rather than crediting. So a state it minted is `PAID` for the rest of the
     * run whatever budget policy the fact-side read uses, and separating the two provenances is the
     * difference between "the pot was too generous" and "this state was never eligible".
     */
    @Volatile
    @JvmField
    var mintedByUnroll: Boolean = false

    /**
     * How many prepends this position has gated, approximately.
     *
     * The population a state governs is the quantity the budget should be spending on, and the
     * manager keeps no fact registry to measure it directly. This is the closest thing it can see:
     * one increment per `writesAbove`, which is called once per prepend above an `[any]`-owning node.
     *
     * Deliberately a plain `Int` and deliberately racy. It is read only to ORDER states inside a
     * re-score, a lost update costs a place in that order, and making it atomic would put a
     * contended write on a path taken twenty million times. Saturating rather than wrapping, because
     * a negative weight would sort a hot state to the front of the budget.
     */
    @JvmField
    var traffic: Int = 0

    /**
     * The transitions out of this state: at most one successor per accessor, which is what keeps the
     * structure deterministic and re-derivation free.
     *
     * Lock-free to read ([ConcurrentReadSafeInt2ObjectMap] captures the backing arrays and retries),
     * written only under the manager lock.
     */
    @Volatile
    @JvmField
    var children: ConcurrentReadSafeInt2ObjectMap<AnyUnrollState>? = null

    /**
     * Incoming edges: accessor -> the representatives with a transition on it INTO this state.
     *
     * The reverse of [children], and it exists because the prepend has to answer *is `a` an incoming
     * edge of the position this fact's `[any]` carries?* at a site with no access to the read that
     * created it. Without it that question needs a single-witness field on the fact, which a merge
     * can silently replace.
     *
     * The value is an IMMUTABLE array, replaced wholesale under the lock, never mutated in place.
     * [ConcurrentReadSafeInt2ObjectMap] re-checks its backing array lengths so a lock-free reader
     * cannot straddle a rehash -- but that protects the MAP, not a mutable value hanging off it. A
     * grow-in-place list would publish an incremented size before the element store was visible and
     * the lock-free backward scan would dereference a null; an in-place `replace` would let a racing
     * scan see one predecessor twice and another never, making the choice among them
     * non-deterministic -- and that choice reaches `AccessNode.anyId`, hence `hash`, hence the merge
     * guard.
     *
     * An accessor with no predecessors left is stored as an EMPTY array rather than removed: fastutil
     * shifts keys on removal, which moves entries within arrays of unchanged length, and that is
     * exactly the one mutation the map's length re-check does not cover.
     */
    @Volatile
    @JvmField
    var parents: ConcurrentReadSafeInt2ObjectMap<Array<AnyUnrollState>>? = null

    /**
     * The representative of this state's DSU class, with path halving.
     *
     * Lock-free and best-effort: a lost halving write is harmless because both racing writers install
     * a link to a genuine ancestor, and ancestors are permanent (a root may acquire a parent, but a
     * non-root never leaves its tree). A stale read costs one extra hop, never a wrong answer.
     */
    fun find(): AnyUnrollState {
        var cur = this
        while (true) {
            val up = cur.parent ?: return cur
            val grand = up.parent ?: return up
            cur.parent = grand
            cur = grand
        }
    }

    override fun toString(): String = "any#$id"
}

/** Same contract as [AnyUnrollState.find], for the dag layer. */
fun AnyUnrollDag.find(): AnyUnrollDag {
    var cur = this
    while (true) {
        val up = cur.parent ?: return cur
        val grand = up.parent ?: return up
        cur.parent = grand
        cur = grand
    }
}

/**
 * The unconditional per-manager population counts behind the progress line.
 *
 * Every one is maintained incrementally at the event, because the manager holds no collection of
 * states or dags -- a registry of states is the one thing that would force weak references back into
 * the design.
 */
data class AnyUnrollLiveStats(
    /** `dagsCreated - dagsFused`: live REPRESENTATIVES, not dags still reachable from a live fact. */
    val liveRoots: Int,
    /** Pots latched past `L`. A transition, not a state, so it needs the per-dag latch. */
    val beyond: Int,
    /** `statesMinted - statesMerged`; `mergeStates` is the only destroyer and removes exactly one. */
    val states: Int,
    val maxStatesPerDag: Int,
    val transitions: Int,
)

/**
 * Process-wide counters for the `[any]` unroll manager, enabled by `-Dopentaint.anyManagerDiag=true`.
 *
 * Every counter is incremented at the event, so nothing has to enumerate states or facts to report
 * them -- which is deliberate: a registry of states is the one thing that would force weak references
 * back into the design.
 */
object AnyUnrollDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.anyManagerDiag")?.trim().toBoolean()

    val mints = AtomicLong()
    val mintsBySite = Array(AnyUnrollManager.MINT_SITE_COUNT) { AtomicLong() }
    val unions = AtomicLong()
    val dagFusions = AtomicLong()
    val transitionsCreated = AtomicLong()
    val reads = AtomicLong()
    val readsReusedFree = AtomicLong()
    val readsRefused = AtomicLong()
    val absorptions = AtomicLong()
    val collapses = AtomicLong()

    /**
     * Of [paidMints], how many came from `readChildPaidOnly` -- the unroll, which stamps `PAID`
     * unconditionally and so cannot be demoted by any policy applied to the fact-side read.
     */
    val paidMintsFromUnroll = AtomicLong()

    /** [AnyUnrollKindPolicy.Rescore]: how often a dag was re-scored, and what it changed. */
    val rescores = AtomicLong()
    val rescoreStatesVisited = AtomicLong()
    val rescoreDemotions = AtomicLong()
    val rescorePromotions = AtomicLong()

    /**
     * The traffic weight the re-score actually saw: the largest on any state it visited, and the sum
     * over the states it demoted. Together they say whether the population ordering reached the hot
     * states or merely reshuffled cold ones.
     */
    val rescoreMaxTraffic = AtomicLong()
    val rescoreDemotedTraffic = AtomicLong()

    /**
     * The COUNTERFACTUAL: for each prepend the kind gate declined, what would have happened if the
     * gate had been open.
     *
     * `writesAbove` returning true is the reason 99.7% of prepends write their step, but "the gate
     * declined" and "the gate is what is costing us" are different claims. These run the rest of the
     * probe -- subtree guard, coverage, and the backward step -- on every declined prepend and record
     * where it would have landed. `cfNoPredecessor` and `cfWouldStay` are the two outcomes that mean
     * the fact pattern was never absorbable in the first place; only `cfWouldMove` is structure the
     * gate is actually holding back.
     */
    val cfDeclinedOrigin = AtomicLong()
    val cfDeclinedPaid = AtomicLong()
    val cfGuardBlocked = AtomicLong()
    val cfUncovered = AtomicLong()
    val cfNoPredecessor = AtomicLong()
    val cfWouldStay = AtomicLong()
    val cfWouldMove = AtomicLong()

    /**
     * Which STATE declined, and how often.
     *
     * The kind is a property of an automaton state, and there are a few hundred of them against
     * millions of prepends, so "how many states decline" and "how many prepends are declined" are
     * different questions with very different answers. Keyed by state id, which is assignment order,
     * so the row also says whether the hot decliners are early mints.
     */
    private val declinesByState = java.util.concurrent.ConcurrentHashMap<Int, java.util.concurrent.atomic.LongAdder>()
    private val declineStateKind = java.util.concurrent.ConcurrentHashMap<Int, String>()

    fun recordDeclineByState(id: Int, kind: String) {
        declinesByState.computeIfAbsent(id) { java.util.concurrent.atomic.LongAdder() }.increment()
        declineStateKind[id] = kind
    }

    private fun declineReport(): String = buildString {
        val all = declinesByState.entries.sortedByDescending { it.value.sum() }
        val total = all.sumOf { it.value.sum() }
        appendLine("ANYUNROLL cf decliningStates=${all.size} declines=$total")
        all.take(12).forEach { (id, n) ->
            val pct = if (total == 0L) "-" else String.format("%.1f%%", 100.0 * n.sum() / total)
            appendLine("ANYUNROLL cf   state#$id kind=${declineStateKind[id]} declines=${n.sum()} ($pct)")
        }
    }

    /** One line per distinct `(outcome, accessor)`, so the fact PATTERN is on the page, not inferred. */
    private const val CF_SAMPLES = 40
    private val cfSamples = java.util.Collections.synchronizedMap(LinkedHashMap<String, String>())

    fun sampleCounterfactual(key: String, render: () -> String) {
        if (!enabled) return
        synchronized(cfSamples) {
            if (cfSamples.size >= CF_SAMPLES || cfSamples.containsKey(key)) return
            cfSamples[key] = render().take(300)
        }
    }

    fun counterfactualReport(): String = buildString {
        appendLine(
            "ANYUNROLL cf declined=[origin:${cfDeclinedOrigin.get()},paid:${cfDeclinedPaid.get()}]" +
                " outcome=[guardBlocked:${cfGuardBlocked.get()},uncovered:${cfUncovered.get()}," +
                "noPredecessor:${cfNoPredecessor.get()},wouldStay:${cfWouldStay.get()}," +
                "wouldMove:${cfWouldMove.get()}]"
        )
        append(declineReport())
        synchronized(cfSamples) { cfSamples.forEach { (k, v) -> appendLine("ANYUNROLL cf   $k | $v") } }
    }

    /**
     * How fast unions move the cut, and in which direction.
     *
     * [kindDemotionsFromOrigin] must read ZERO once `ORIGIN` is neutral -- non-zero means a fresh
     * start state is carrying an opinion it never bought, and at 98.8% cross-dag fusion traffic that
     * one bug decides the cut instead of the knob. [kindDemotionsGenuine] is the only evidence about
     * the knob: a `PAID` state in one automaton paired with a `CREDIT` state in the other, requiring
     * both to have materialised the same sequence, one before its ceiling and one after.
     */
    /** How much of the automaton is unpaid. `creditMints >> paidMints` means `L` is small for the workload. */
    val paidMints = AtomicLong()
    val creditMints = AtomicLong()

    /**
     * §5.8(i): IS THE FORK REAL? Absorbs where the backward step found more than one predecessor.
     *
     * `y.parent = x` re-points every predecessor of `y` onto `x`, so two automata that each had an
     * `a`-predecessor leave `x.parents[a]` holding both -- and 11,482 of 11,625 thingsboard unions
     * are cross-dag fusions. That is a PREDICTION about the reverse index, not a measurement, and
     * these two counters are what would establish it. Near zero means a greedy pick is the design and
     * the subset construction should not be built at all.
     */
    val absorbForkHits = AtomicLong()
    val absorbForkMaxWidth = AtomicLong()

    /**
     * Folds that stopped absorbing with links still above them -- what the subset step should remove.
     *
     * The split is the decisive one for §5.8. A fold that stalls having made NO step was standing on
     * a single state, where a set of positions cannot exist yet and the subset construction can do
     * nothing. Only [telescopeStallsAfterStep] -- a fold that got somewhere and then dead-ended -- is
     * the population a lazy determinisation could rescue, and the fork is a candidate explanation for
     * it only there.
     */
    val telescopeStalls = AtomicLong()
    val telescopeStallsAfterStep = AtomicLong()
    val telescopeSteps = AtomicLong()

    /** Is the backward query hitting? `absorbStay` dominant means the compression did not land. */
    val absorbExact = AtomicLong()
    val absorbStay = AtomicLong()

    /**
     * The targeting split -- structure KEPT that a budget-only form would drop. This is the number
     * that justifies the design over "route every prepend through the existing absorb".
     */
    val prependWrittenPaid = AtomicLong()
    val prependWrittenCreditMismatch = AtomicLong()

    /** §4.3's GUARD declining, and an uncovered accessor: both write, neither is a mismatch. */
    val prependGuardBlocked = AtomicLong()
    val prependUncovered = AtomicLong()

    /**
     * Element absorption is ON, and this is the `[].[any].[]` case the subtree probe covers.
     *
     * `manager.create(elementAccess = limitElementAccess(...))` resolves to
     * `create(ELEMENT_ACCESSOR_IDX, it)` and `limitElementAccess` never returns null, so the element
     * arm goes through the funnel; `ElementAccessor` is covered. `limitElementAccess` caps only
     * CONSECUTIVE element runs, so unlike fields this shape really is constructible.
     */
    val elementPrependOverAny = AtomicLong()

    /**
     * The graft pre-pass: absorptions taken in `bulkMergeAddAccessors`, the commit the design exists
     * for, and the falsifier for the depth-relative claim it does not report.
     *
     * [graftAbsorbUnderClaim] MUST STAY ZERO. Both callers hand this rewrite a receiver whose own
     * `deepAccessorExclusion` is null -- `concat`'s is a freshly created node, `addParentFieldAccess`'s
     * comes out of `create` -- so no depth-1 claim is in scope to be disturbed. A non-zero reading
     * means one reached it after all, and the per-branch report is genuinely owed.
     */
    val graftAbsorbs = AtomicLong()
    val graftAbsorbUnderClaim = AtomicLong()

    /**
     * Absorptions taken while folding a premise chain back into a fact
     * (`createAbstractNodeFromReversedAp` / `createAbstractNodeFromAccessors`).
     *
     * Census row 1 puts both folds in the funnel, and the fold that matters is the initial-fact
     * abstraction's emission: read and prepend are co-located there too, so the rule will fire, and
     * firing UNDOES the enumeration the abstraction just paid for. Sound -- coarsening an emitted
     * fact is a superset -- but it is the same shape row 5 is excluded for, one level up. Counted
     * separately so the two are not confused in `absorptions`.
     */
    val chainFoldAbsorbs = AtomicLong()

    /**
     * What the row-5 exclusion actually saved: prepends where the abstraction's own unroll WOULD have
     * absorbed the accessor it had just read.
     *
     * Deliberately not a "must stay zero" counter. Because the abstraction passes `absorbing = false`
     * the funnel is structurally unreachable from it, so a zero would be guaranteed by construction
     * and would say nothing -- the failure mode an earlier mint-site split already hit. This measures
     * the exclusion instead of asserting it.
     */
    val tifaAbsorbSuppressed = AtomicLong()

    /** Lemma 9.2 and the racing window of the incoming remap. Should be small. */
    val witnessForwardCheckFailed = AtomicLong()

    /**
     * The §8.1 identity, asserted on real workloads rather than in a unit test: at
     * `filterStartsWith`'s fold the backward query must return the state the caller already threaded.
     * MUST STAY ZERO -- a non-zero reading falsifies Lemma 9.2 in production, where no test reaches.
     *
     * **It was structurally zero until 2026-08-26.** The counter was declared and reported and never
     * incremented, so every result document that read its zero as evidence read nothing at all. It is
     * wired at [AccessTree.AccessNode.filterStartsWithImpl]'s shadow telescope now.
     */
    val witnessDisagreesWithThreadedState = AtomicLong()

    /**
     * Forks whose candidates do NOT all carry the same [AnyUnrollKind] -- the ONLY consequence the
     * choice among them can have.
     *
     * A fork cannot move a fact between pots: `mint` gives a child its parent's dag and only `union`
     * fuses dags, so a state's dag IS its reachability component and every predecessor of a state is
     * necessarily inside it. The pick therefore cannot change `budgetExhausted`, the charge, or which
     * origin pays. What it CAN change is the kind of the position the fact lands on, and the kind is
     * what [writesAbove] gates the NEXT prepend on. When every candidate agrees on kind, greedy and
     * any other rule are indistinguishable to everything downstream.
     *
     * This is the number that decides whether design §5.8 has an unmeasured justification. The
     * measurement that retired §5.8 counted STALLS, which bounds only telescope completeness -- a
     * fork never stalls, it succeeds, at a state chosen for no reason.
     */
    val absorbForkKindSplit = AtomicLong()

    /** Forks where a self-loop was among the candidates, i.e. where "absorb and stay" was available. */
    val absorbForkSelfLoopPreferred = AtomicLong()

    /**
     * Forks where the ranked selector landed somewhere the old min-id pick would not have. The direct
     * "did this change anything" number; bounded above by [absorbForkHits].
     */
    val absorbForkChoiceChanged = AtomicLong()

    /**
     * The population excluded from [witnessDisagreesWithThreadedState]: the backward query answered
     * with a SELF-LOOP where the descent had threaded a different predecessor. The rank prefers the
     * self-loop on purpose, so this is the selector working, not the lemma failing.
     */
    val witnessSelfLoopPreferred = AtomicLong()

    /**
     * A telescope that stalled one step after crossing a state that HAD a fork -- the only population
     * design §5.8's subset construction can rescue, and the one thing [telescopeStallsAfterStep]
     * was being read as a proxy for.
     */
    val telescopeStallAfterFork = AtomicLong()

    /**
     * Telescope probes that had no `[any]` position to start from at all (`probe == null`).
     *
     * Until 2026-08-26 these were counted as [telescopeStalls], which is why 97-98% of stalls looked
     * like first-link stalls: a descent that ended on a node carrying no `[any]` cannot telescope and
     * is not a targeting refusal. The two populations are separated now; only the remainder is a
     * statement about the automaton.
     */
    val telescopeNoPosition = AtomicLong()

    fun recordFork(width: Int) {
        var cur = absorbForkMaxWidth.get()
        while (width > cur && !absorbForkMaxWidth.compareAndSet(cur, width.toLong())) cur = absorbForkMaxWidth.get()
    }

    val kindPromotions = AtomicLong()
    val kindDemotionsGenuine = AtomicLong()
    val kindDemotionsFromOrigin = AtomicLong()

    /**
     * Facts materialised by the initial-fact abstraction's unroll -- one per `accountUnrolledFact()`
     * in the retired per-`(entry point, base)` counter.
     *
     * It exists to measure the gap between what that counter charged and what the manager charges.
     * The old counter charged once per materialised FACT, at every position, every time; the manager
     * charges once per distinct `(state, accessor)` TRANSITION, and re-deriving a recorded path is
     * free by design. Those two coincide only when paths are not re-derived at many positions, so
     * the ratio is the honest measure of how much weaker the new cut is per unit of work.
     */
    val tifaUnrolledFacts = AtomicLong()

    /**
     * The largest `total` any pot ever reached, and how many reads the single worst pot refused.
     *
     * The aggregate counters cannot tell "every pot is at its limit" from "one giant pot is at its
     * limit and refuses half the program", and those two call for opposite responses: the first says
     * the limit is too low, the second says the cut is landing on one origin and the lever is that
     * origin rather than its budget.
     */
    val maxPotTotal = AtomicLong()
    val maxPotRefusals = AtomicLong()

    fun recordPot(total: Int) {
        var cur = maxPotTotal.get()
        while (total > cur && !maxPotTotal.compareAndSet(cur, total.toLong())) cur = maxPotTotal.get()
    }

    /** §12.1: the union-without-collapse arm, broken down by the accessor that separates the two. */
    val unionWithoutCollapseMark = AtomicLong()
    val unionWithoutCollapseStatic = AtomicLong()
    val unionWithoutCollapseTypeInfo = AtomicLong()
    val unionWithoutCollapseOther = AtomicLong()

    /**
     * §12.5: reads taken through the QUERY entry point.
     *
     * It counts CALLS, not records -- a query never records, by construction, so a "must stay at
     * zero" reading of it is permanently red and meaningless. What it is actually for is spotting a
     * caller misclassified the other way: a build treated as a query under-charges, and a large
     * `queryReads` against a small `reads` is what that looks like.
     */
    val queryReads = AtomicLong()

    fun report(): String = buildString {
        append("anyUnroll ")
        append("mints=").append(mints.get())
        append(" mintsBySite=").append(
            AnyUnrollManager.MINT_SITE_NAMES.withIndex()
                .joinToString(",") { (i, n) -> "$n:${mintsBySite[i].get()}" }
        )
        append(" unions=").append(unions.get())
        append(" dagFusions=").append(dagFusions.get())
        append(" transitions=").append(transitionsCreated.get())
        append(" reads=").append(reads.get())
        append(" reusedFree=").append(readsReusedFree.get())
        append(" refused=").append(readsRefused.get())
        append(" absorptions=").append(absorptions.get())
        append(" collapses=").append(collapses.get())
        append(" tifaFacts=").append(tifaUnrolledFacts.get())
        append(" maxPotTotal=").append(maxPotTotal.get())
        append(" maxPotRefusals=").append(maxPotRefusals.get())
        append(" unionNoCollapse=[mark:").append(unionWithoutCollapseMark.get())
        append(",static:").append(unionWithoutCollapseStatic.get())
        append(",typeInfo:").append(unionWithoutCollapseTypeInfo.get())
        append(",other:").append(unionWithoutCollapseOther.get())
        append("]")
        append(" rescore=[n:").append(rescores.get())
        append(",maxTraffic:").append(rescoreMaxTraffic.get())
        append(",demotedTraffic:").append(rescoreDemotedTraffic.get())
        append(",visited:").append(rescoreStatesVisited.get())
        append(",demote:").append(rescoreDemotions.get())
        append(",promote:").append(rescorePromotions.get())
        append("]")
        append(" queryReads=").append(queryReads.get())
        append(" mintKind=[paid:").append(paidMints.get())
        append("(unroll:").append(paidMintsFromUnroll.get()).append(")")
        append(",credit:").append(creditMints.get())
        append("]")
        append(" prepend=[absorbExact:").append(absorbExact.get())
        append(",absorbStay:").append(absorbStay.get())
        append(",writtenPaid:").append(prependWrittenPaid.get())
        append(",writtenMismatch:").append(prependWrittenCreditMismatch.get())
        append(",guardBlocked:").append(prependGuardBlocked.get())
        append(",uncovered:").append(prependUncovered.get())
        append(",element:").append(elementPrependOverAny.get())
        append(",graft:").append(graftAbsorbs.get())
        append(",chainFold:").append(chainFoldAbsorbs.get())
        append(",tifaSuppressed:").append(tifaAbsorbSuppressed.get())
        append(",graftUnderClaim:").append(graftAbsorbUnderClaim.get())
        append("]")
        append(" fork=[hits:").append(absorbForkHits.get())
        append(",maxWidth:").append(absorbForkMaxWidth.get())
        append(",telescopeSteps:").append(telescopeSteps.get())
        append(",telescopeStalls:").append(telescopeStalls.get())
        append(",telescopeStallsAfterStep:").append(telescopeStallsAfterStep.get())
        append(",telescopeNoPosition:").append(telescopeNoPosition.get())
        append(",kindSplit:").append(absorbForkKindSplit.get())
        append(",selfLoopAvailable:").append(absorbForkSelfLoopPreferred.get())
        append(",choiceChanged:").append(absorbForkChoiceChanged.get())
        append(",stallAfterFork:").append(telescopeStallAfterFork.get())
        append("]")
        append(" witness=[fwdCheckFailed:").append(witnessForwardCheckFailed.get())
        append(",disagrees:").append(witnessDisagreesWithThreadedState.get())
        append(",selfLoopPreferred:").append(witnessSelfLoopPreferred.get())
        append("]")
        append(" kind=[promote:").append(kindPromotions.get())
        append(",demoteGenuine:").append(kindDemotionsGenuine.get())
        append(",demoteFromOrigin:").append(kindDemotionsFromOrigin.get())
        append("]")
    }
}

/**
 * Allocation, union and charging for the `[any]` unroll automata. One per [TreeApManager].
 *
 * Ownership lives here rather than on the nodes because [TreeApManager] is the single object every
 * tree-backend site already holds, and it is the only common ancestor of the two spend sites, which
 * live under different owners (the abstraction under the callee's analyzer, the subscription under
 * the caller's).
 *
 * ## Threading
 *
 * `find` is lock-free on the hot path; every MUTATION -- a union, a new transition, a charge -- runs
 * inside [lock]. That is not a performance choice: two threads racing `union(x, y)` and `union(y, x)`
 * can each observe two distinct roots and write `a.parent = b` and `b.parent = a`, leaving a CYCLE in
 * the DSU forest that nothing detects and that makes every subsequent `find` spin forever. A root
 * discovered under the lock is still a root when it is written, which is what keeps the forest
 * acyclic. Halving stays lock-free because its write set (non-roots whose parent is also a non-root)
 * is disjoint from union's (roots only).
 */
class AnyUnrollManager(
    /** `L`. Negative means the feature is off: no states, no records, no refusals. */
    @JvmField val limit: Int,
    /**
     * What kind the survivor of a union carries. Fixed for the run -- every termination argument
     * here assumes at most two kind transitions per state, which a strategy that changed mid-run
     * would break.
     */
    @JvmField val kindMerge: AnyUnrollKindMerge = DEFAULT_KIND_MERGE,
    /** Which pot the mint compares against; see [AnyUnrollKindPolicy]. Fixed for the run. */
    @JvmField val kindPolicy: AnyUnrollKindPolicy = DEFAULT_KIND_POLICY,
    /** The order a re-score spends its budget in; see [AnyUnrollRescoreStrategy]. Fixed for the run. */
    @JvmField val rescoreStrategy: AnyUnrollRescoreStrategy = DEFAULT_RESCORE_STRATEGY,
    /**
     * What one materialised accessor sequence costs the pot: its LENGTH (default) or a flat 1.
     *
     * See [DEFAULT_PATH_LENGTH_COST]. Fixed for the run -- a budget whose unit changed mid-run would
     * make `total` a mixture of two quantities and `total >= limit` unreadable.
     */
    @JvmField val pathLengthCost: Boolean = DEFAULT_PATH_LENGTH_COST,
) {
    val enabled: Boolean get() = limit >= 0

    private val lock = Any()
    private val stateIds = AtomicInteger()
    private val dagIds = AtomicInteger()

    /* ---------- the progress-line counters (unconditional, per manager) ---------- */

    // Four increments on paths that already do atomic work, and they are NOT gated on
    // `anyManagerDiag`: the line they feed is the only thing that separates failure modes an
    // aggregate cannot -- "origins proliferating, none spending" from "a few origins absorbing the
    // whole program" -- and a diagnostic nobody turns on does not separate them on a real run.
    //
    // Counting without a registry. `newOrigin` is the only creator of a dag and the cross-dag fusion
    // the only destroyer, and a fusion removes exactly one representative, so live roots are
    // `dagsCreated - dagsFused`. States follow the same shape against `mergeStates`. Exhaustion is a
    // TRANSITION rather than a state, so it needs the per-dag latch [AnyUnrollDag.exhaustedCounted].
    private val dagsCreated = AtomicInteger()
    private val dagsFused = AtomicInteger()
    private val dagsExhausted = AtomicInteger()
    private val statesMinted = AtomicInteger()
    private val statesMerged = AtomicInteger()
    private val maxStatesPerDag = AtomicInteger()
    private val transitionsInstalled = AtomicInteger()

    /**
     * Incoming-remap steps declined because the predecessor's real forward edge resolved elsewhere.
     *
     * MEASURED, NOT ZERO: 17 in a conductor run holding 12,677 transitions, 0.13%. An earlier comment
     * here claimed the case was unreachable if the mirror was exact; it is not. It is the drain
     * window `mergeStates` opens on itself -- the conflict arm QUEUES a pair rather than writing the
     * transition, so between the queueing and the drain a predecessor listed in `parents` genuinely
     * does point somewhere that has not been unified yet.
     *
     * Skipping is the arm that cannot DROP a transition, and it is self-healing: the queued merge
     * eventually runs, and its own incoming remap moves that predecessor onto the winner. Until then
     * the backward query simply misses the edge, which makes it decline to absorb -- the sound
     * direction.
     */
    private val remapConflicts = AtomicInteger()

    /** `pathCount` saturates here: past `L` the state refuses everything anyway. */
    private val pathCountCeiling: Int = if (limit <= 0) 1 else limit

    /**
     * `lengthSum` saturates here.
     *
     * NOT `pathCountCeiling`: a state may legitimately be reached by `L` words of length `L`, so the
     * length sum lives a whole factor of `L` above the word count and clamping it at `L` would make
     * every deep state look like a shallow one. The ceiling exists only to keep the charge inside
     * `Int` -- any pot whose length sum reaches it is far past `L` and refuses everything already.
     */
    private val lengthSumCeiling: Int = Int.MAX_VALUE / 2

    /** The [AnyUnrollKindPolicy.Global] pot. Written only under [lock], beside `dag.total`. */
    private var globalSpend: Int = 0

    /** Diagnostics only; see [newOrigin]. Keyed by the dag's own id, never by its representative. */
    private val dagRegistry = java.util.concurrent.ConcurrentHashMap<Int, AnyUnrollDag>()

    /**
     * The pots, as they stand at the end of the run: one row per surviving representative.
     *
     * The question this exists for is whether a re-score triggered by "this dag's total crossed `L`"
     * could ever reach the states that actually decline. It can only reach a state whose dag crossed,
     * so the distribution of `total` across dags -- not the maximum, which is what the progress line
     * reports -- is what decides it.
     */
    fun dagCensus(): String {
        if (!enabled) return ""
        val reps = LinkedHashMap<Int, AnyUnrollDag>()
        for (dag in dagRegistry.values) {
            val rep = dag.find()
            reps[rep.id] = rep
        }
        val rows = reps.values.sortedByDescending { it.total }
        val crossed = rows.count { it.total >= limit }
        return buildString {
            appendLine(
                "ANYUNROLL dags live=${rows.size} crossedLimit=$crossed limit=$limit" +
                    " totals=[${rows.take(12).joinToString(",") { "${it.total}/${it.states}" }}]" +
                    " (total/states, largest first)"
            )
            val hist = IntArray(7)
            for (r in rows) {
                val b = when {
                    r.total >= limit -> 6
                    r.total >= limit / 2 -> 5
                    r.total >= limit / 4 -> 4
                    r.total >= limit / 8 -> 3
                    r.total >= 4 -> 2
                    r.total >= 2 -> 1
                    else -> 0
                }
                hist[b]++
            }
            appendLine(
                "ANYUNROLL dags byTotal=[<2:${hist[0]},2-3:${hist[1]},4-L/8:${hist[2]}," +
                    "L/8-L/4:${hist[3]},L/4-L/2:${hist[4]},L/2-L:${hist[5]},>=L:${hist[6]}]"
            )
        }
    }

    /** The dag a state belongs to, for the decline census. */
    fun dagOf(state: AnyUnrollState?): AnyUnrollDag? =
        if (!enabled || state == null) null else state.find().dag.find()

    /** R1: a fresh origin -- a new dag with `total = 0` and its root state with `pathCount = 1`. */
    fun newOrigin(site: Int): AnyUnrollState? {
        if (!enabled) return null

        val dag = AnyUnrollDag(dagIds.incrementAndGet())
        val root = AnyUnrollState(stateIds.incrementAndGet(), dag)
        dag.rootState = root
        dag.states = 1
        dag.nextRescoreAt = maxOf(1, limit)
        dagsCreated.incrementAndGet()
        statesMinted.incrementAndGet()
        noteMaxStates(1)
        // A fresh pot can be born exhausted: at `L = 0` every origin is already at its limit, and
        // the latch has to see that or `beyond` reads zero on the arm where it matters most.
        noteTotal(dag)

        if (AnyUnrollDiagnostics.enabled) {
            AnyUnrollDiagnostics.mints.incrementAndGet()
            AnyUnrollDiagnostics.mintsBySite[site].incrementAndGet()
            // The manager keeps no dag registry by design; this one exists only under the diagnostic
            // flag, and only so the pots can be censused. `find()` at report time collapses the
            // fused ones, so holding every dag ever created costs a few hundred entries.
            dagRegistry[dag.id] = dag
        }

        return root
    }

    /**
     * R2/R3: make [a] and [b] one manager, preferring [a]'s representative.
     *
     * Receiver preference is semantically neutral -- the union merges the two states by product, so
     * the content is identical whichever survives -- but it is not neutral for speed. In `mergeAdd`
     * the receiver is the accumulated, long-lived tree, so keeping its representative means the
     * stored node's id does not change, the merge guard's `===` fires on the SAME round, and the fact
     * stays out of the worklist. Preferring the arrival would cost an extra fixpoint lap for every
     * folded loop in the program.
     */
    fun union(a: AnyUnrollState?, b: AnyUnrollState?): AnyUnrollState? {
        if (!enabled) return null
        if (a == null) return b
        if (b == null) return a
        if (a === b) return a

        // Lock-free, and it carries the steady state. Receiver preference keeps the accumulated
        // tree's STORED reference unchanged while the arrival's is absorbed, and node identity
        // compares stored references -- so "two distinct objects with the same representative" is
        // the normal case, not the exception. Without this every merge of two `[any]`-carrying nodes
        // would take the per-manager monitor on the hottest path in the analyzer just to discover
        // there is nothing to do. The DSU only ever moves towards a root, so a stale negative simply
        // falls through to the locked path.
        val fastA = a.find()
        val fastB = b.find()
        if (fastA === fastB) return fastA

        synchronized(lock) {
            var x = a.find()
            var y = b.find()
            if (x === y) return x

            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.unions.incrementAndGet()

            val dx = x.dag.find()
            val dy = y.dag.find()
            if (dx !== dy) {
                // Two automata in, one automaton out: the pots combine and the START states merge,
                // so the result is a single deterministic structure rather than two sharing a pot.
                // Summing over-states by the sequences the two had in common, which refuses sooner
                // -- the sound direction -- and avoids a full product traversal on a rare path.
                val dyRoot = dy.rootState
                dy.parent = dx
                dx.total = satAdd(dx.total, dy.total, Int.MAX_VALUE)
            // A fusion is the other way a pot crosses its limit. `maxOf`, not `minOf`: a fresh `dy`
            // carries `nextRescoreAt = L`, so taking the minimum would drag a survivor already at
            // four times `L` back to re-scoring on its very next mint, once per fusion -- and a
            // re-score is now a list allocation and a sort, under the global lock.
            dx.nextRescoreAt = maxOf(dx.nextRescoreAt, dy.nextRescoreAt)
                dx.states = satAdd(dx.states, dy.states, Int.MAX_VALUE)
                noteMaxStates(dx.states)

                // The part that is easy to get wrong: the pots SUM, so a fusion can push the
                // survivor over the limit on its own AND remove a dag that was already counted.
                dagsFused.incrementAndGet()
                when {
                    dy.exhaustedCounted && dx.exhaustedCounted -> dagsExhausted.decrementAndGet()
                    dy.exhaustedCounted -> dx.exhaustedCounted = true
                }
                noteTotal(dx)

                if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.dagFusions.incrementAndGet()

                val dxRoot = dx.rootState
                if (dxRoot != null && dyRoot != null) {
                    // accumulatePaths = FALSE. Both start states denote the EMPTY sequence, so
                    // merging them leaves one state reached by one sequence, not two -- and the same
                    // holds all the way down the cascade, which pairs states reached by the SAME
                    // accessor sequence in the two automata. The merged path set is the union of two
                    // sets that overlap by construction, so `max` is the right operator and `sum`
                    // over-states it by the whole overlap.
                    //
                    // Measured, before this was fixed: 11,482 of 11,625 unions on thingsboard were
                    // cross-dag fusions, so root path counts saturated at `L` and a component of a
                    // hundred fused origins refused on its FIRST new accessor. 1,323 transitions
                    // across ~690 pots -- under two each -- produced 16,792 refusals at L = 100.
                    mergeStates(dxRoot.find(), dyRoot.find(), accumulatePaths = false)
                }

                // The fusion may already have merged x and y transitively.
                x = a.find()
                y = b.find()
                if (x === y) return x
            }

            // A same-dag union DOES accumulate: `x` and `y` are different positions in one
            // automaton, so the sequences reaching them are genuinely different sequences, and one
            // new transition out of the merged state authorises all of them.
            return mergeStates(x, y, accumulatePaths = true)
        }
    }

    /**
     * The product merge. Both operands must be representatives of the SAME dag.
     *
     * The union is performed IN PLACE, which is why no separate `memo[(x, y)]` is needed to break
     * cycles: `y.parent = x` is itself the memo, and re-encountering the pair short-circuits on
     * `find(x) === find(y)`. Each productive union reduces the number of live representatives by
     * one, so the loop terminates on a cyclic structure for the same reason a memoised product does.
     *
     * The invariant that makes the lock-free read correct: **only a representative carries
     * transitions**. A state that loses root status has its child map folded into the winner in the
     * same step, so a reader that resolves `find()` and reads that state's `children` never lands on
     * an orphaned map. A reader racing the fold sees the transition missing, falls to the slow path,
     * takes the lock -- which the fold holds -- and re-resolves.
     */
    private fun mergeStates(
        x0: AnyUnrollState,
        y0: AnyUnrollState,
        accumulatePaths: Boolean,
    ): AnyUnrollState {
        val pending = ArrayDeque<AnyUnrollState>()
        pending.addLast(x0)
        pending.addLast(y0)

        while (pending.isNotEmpty()) {
            val x = pending.removeFirst().find()
            val y = pending.removeFirst().find()
            if (x === y) continue

            y.parent = x
            mergeKind(x, y)
            statesMerged.incrementAndGet()
            x.dag.find().states--
            x.pathCount = if (accumulatePaths) {
                satAdd(x.pathCount, y.pathCount, pathCountCeiling)
            } else {
                maxOf(x.pathCount, y.pathCount)
            }
            // Follows `pathCount` exactly, and for the same reason: accumulating when the two states
            // are reached by genuinely different sequences, `max` when the cascade has paired states
            // reached by the SAME sequence in two fused automata and the union overlaps by
            // construction. Note that the merge moves NO cost: `dag.total` is an accumulator over
            // mint EVENTS, so folding two states leaves it exactly where it was. That is what keeps
            // the measure monotone where recomputing "sum of path lengths" over the merged structure
            // would not be -- collapsing a chain into a self-loop would hand budget BACK.
            x.lengthSum = if (accumulatePaths) {
                satAdd(x.lengthSum, y.lengthSum, lengthSumCeiling)
            } else {
                maxOf(x.lengthSum, y.lengthSum)
            }
            // Traffic ALWAYS accumulates, however the paths merge: the merged state now gates every
            // prepend both of them gated, which is exactly what the weight is meant to say.
            x.traffic = satAdd(x.traffic, y.traffic, Int.MAX_VALUE)

            // (1) INCOMING. Nothing used to touch the states pointing AT `y`, so a predecessor's
            // transition named the loser verbatim, forever -- and held it against the collector.
            // Every such edge is re-pointed at `x`, which both closes that retention hole and makes
            // the backward query complete, so no single-witness record is needed and no merge can
            // silently replace one.
            //
            // This writes ANOTHER state's `children`, which is safe for the reason the outgoing fold
            // below documents: if `pr` later loses root status, its children -- including the entry
            // just written -- are folded into the new winner by exactly this code.
            //
            // `putTransition`, not `pr.children?.put`: the latter no-ops when `children` is null,
            // which a representative that never carried transitions of its own legitimately is.
            val incoming = y.parents
            if (incoming != null) {
                y.parents = null
                val inKeys = incoming.keys.toIntArray()
                for (accessor in inKeys) {
                    val preds = incoming.get(accessor) ?: continue
                    for (pred in preds) {
                        // A self-loop on `y` resolves to `x` here and is reinstalled as a self-loop
                        // on `x` -- which is what the loop it records means, and what makes the next
                        // read of that accessor free.
                        val pr = pred.find()
                        val forward = pr.children?.get(accessor)
                        if (forward == null || forward.find() === x) {
                            putTransition(pr, accessor, x)
                        } else {
                            // The drain window this loop opens on itself: the conflict arm below
                            // QUEUES a pair rather than writing the transition, so a predecessor
                            // listed in `y.parents` can genuinely point at a state that has not been
                            // unified with `x` yet. Skipping rather than overwriting is the arm that
                            // cannot DROP a transition, and it is self-healing -- the queued merge
                            // runs later and its own remap moves that predecessor onto the winner.
                            // Until then the backward query misses the edge and declines to absorb,
                            // which is the sound direction. Measured at 0.13% of transitions.
                            remapConflicts.incrementAndGet()
                        }
                    }
                }
            }

            val absorbed = y.children ?: continue
            y.children = null

            // `x` is still a root here (nothing above has repointed it), but it may stop being one
            // later in this same loop -- at which point ITS children are folded into the new winner
            // by exactly this code. So writing here is safe.
            val keys = absorbed.keys.toIntArray()
            for (accessor in keys) {
                val target = absorbed.get(accessor) ?: continue
                val rep = target.find()

                // (2) OUTGOING, the mirror only. `y` has stopped being a representative, so its name
                // must not survive as a value in any `parents` array -- invariant (I). The new edge
                // is added by the `putTransition` below, or is already there in the conflict arm.
                removeParentEdge(rep, accessor, y)

                val existing = x.children?.get(accessor)
                if (existing == null) {
                    // One successor per accessor: an NFA here would make every lookup explore a SET
                    // of states, re-derivation would stop being free, and the whole design collapses.
                    putTransition(x, accessor, rep)
                } else {
                    // The conflict arm does NOT call `putTransition` -- it queues the pair -- so
                    // between here and the drain of `pending` a lock-free backward scan can observe
                    // a predecessor whose forward edge does not yet resolve back. Sound, and it is
                    // why the backward query re-checks the forward direction: that turns the window
                    // into a MISS rather than a wrong predecessor.
                    pending.addLast(existing)
                    pending.addLast(target)
                }
            }
        }

        return x0.find()
    }

    /**
     * Install `state --accessor--> target`, and its mirror in [AnyUnrollState.parents].
     *
     * The two directions are written together at every call site, which is what makes invariant (I)
     * a property of one function rather than a convention spread over the file.
     */
    private fun putTransition(state: AnyUnrollState, accessor: AccessorIdx, target: AnyUnrollState) {
        val existing = state.children
        if (existing != null) {
            if (existing.put(accessor, target) == null) transitionsInstalled.incrementAndGet()
        } else {
            val map = ConcurrentReadSafeInt2ObjectMap<AnyUnrollState>()
            map.put(accessor, target)
            transitionsInstalled.incrementAndGet()
            state.children = map
        }
        addParentEdge(target, accessor, state)
    }

    /**
     * The survivor's kind. This choice does NOT affect which object survives -- that is [union]'s
     * receiver preference, a separate and non-negotiable requirement -- only what the survivor says
     * about itself.
     */
    /**
     * Re-assign this dag's kinds so that a BOUNDED sub-automaton stays `PAID` and the rest is
     * `CREDIT`.
     *
     * The shipped rule stamps a kind at the mint and never revisits it, so a state minted while the
     * pot was solvent stays `PAID` even after the pot has gone to four times the limit. On conductor
     * that is not a corner case: one dag of 140 reaches `total = 401` against `L = 100`, and the
     * states declining 82% of all absorptions live in it.
     *
     * The states are always ENUMERATED breadth-first -- the automaton is allowed to be cyclic, so the
     * traversal needs the seen-set either way -- and [AnyUnrollRescoreStrategy] decides the order the
     * budget is SPENT in. Each state is charged the same `pathCount` the mint charges, and the states
     * the budget covers, as a prefix of that order, keep `PAID`.
     *
     * Caller holds [lock]. `ORIGIN` is left alone -- it is the neutral element of the kind lattice
     * and an origin has no predecessor to absorb into anyway.
     */
    private fun rescoreDag(dag: AnyUnrollDag) {
        val root = dag.rootState?.find() ?: return

        var budget = limit
        val seen = java.util.Collections.newSetFromMap(java.util.IdentityHashMap<AnyUnrollState, Boolean>())
        val queue = ArrayDeque<AnyUnrollState>()
        queue.addLast(root)
        seen.add(root)

        // Enumerate breadth-first in both strategies -- the automaton may be cyclic, so the traversal
        // needs the `seen` guard either way -- and let the strategy decide the SPENDING order.
        val order = ArrayList<AnyUnrollState>()
        while (queue.isNotEmpty()) {
            val state = queue.removeFirst()
            order.add(state)
            state.children?.forEachEntry { _, child ->
                val target = child.find()
                if (seen.add(target)) queue.addLast(target)
            }
        }
        if (rescoreStrategy == AnyUnrollRescoreStrategy.Population) {
            // Least-trafficked first: the budget buys precision where precision is cheap, and the
            // states gating millions of prepends fall out of it and become eligible to absorb.
            //
            // The key is SNAPSHOT, not read through the comparator. `traffic` is written lock-free by
            // `writesAbove` while this runs under the lock, and a key that moves during a sort is an
            // inconsistent comparator -- for 32 elements or more TimSort detects it and throws
            // `IllegalArgumentException` out of the mint, which would abort `mint` after the
            // transition was installed and leave `dag.states` permanently wrong.
            val weight = java.util.IdentityHashMap<AnyUnrollState, Int>(order.size)
            for (state in order) weight[state] = state.traffic
            order.sortBy { weight[it] ?: 0 }
        }

        var visited = 0
        var demoted = 0
        var promoted = 0
        var demotedTraffic = 0L
        var exhausted = false

        for (state in order) {
            visited++

            if (state.kind != AnyUnrollKind.ORIGIN) {
                val cost = state.pathCount
                val before = state.kind
                // A PREFIX, not a greedy knapsack. Once one state does not fit, every state after it
                // in the order is `CREDIT` too -- otherwise a cheap state further down the order is
                // still kept `PAID`, and under `Population` "further down the order" means "gates
                // more traffic", which is exactly what the strategy exists to demote.
                if (!exhausted && budget >= cost) {
                    state.kind = AnyUnrollKind.PAID
                    budget -= cost
                } else {
                    exhausted = true
                    state.kind = AnyUnrollKind.CREDIT
                }
                if (state.kind != before) {
                    if (state.kind == AnyUnrollKind.CREDIT) {
                        demoted++
                        demotedTraffic += state.traffic
                    } else {
                        promoted++
                    }
                }
            }
        }

        dag.nextRescoreAt = maxOf(limit, satAdd(dag.total, dag.total, Int.MAX_VALUE))

        if (AnyUnrollDiagnostics.enabled) {
            AnyUnrollDiagnostics.rescores.incrementAndGet()
            AnyUnrollDiagnostics.rescoreStatesVisited.addAndGet(visited.toLong())
            AnyUnrollDiagnostics.rescoreDemotions.addAndGet(demoted.toLong())
            AnyUnrollDiagnostics.rescorePromotions.addAndGet(promoted.toLong())
            val maxTraffic = order.maxOfOrNull { it.traffic.toLong() } ?: 0L
            AnyUnrollDiagnostics.rescoreMaxTraffic.updateAndGet { prev -> maxOf(prev, maxTraffic) }
            AnyUnrollDiagnostics.rescoreDemotedTraffic.addAndGet(demotedTraffic)
        }
    }

    private fun mergeKind(x: AnyUnrollState, y: AnyUnrollState) {
        val before = x.kind
        val after = when {
            x.kind == AnyUnrollKind.ORIGIN -> y.kind
            y.kind == AnyUnrollKind.ORIGIN -> x.kind
            kindMerge == AnyUnrollKindMerge.PreferBelow -> minOf(x.kind, y.kind)
            else -> maxOf(x.kind, y.kind)
        }
        if (after == before) return
        x.kind = after

        if (!AnyUnrollDiagnostics.enabled) return
        when {
            after > before -> AnyUnrollDiagnostics.kindPromotions
            before == AnyUnrollKind.ORIGIN -> AnyUnrollDiagnostics.kindDemotionsFromOrigin
            else -> AnyUnrollDiagnostics.kindDemotionsGenuine
        }.incrementAndGet()
    }

    /** Copy-on-write: the array a lock-free scan may already be holding is never touched. */
    private fun addParentEdge(state: AnyUnrollState, accessor: AccessorIdx, pred: AnyUnrollState) {
        val map = state.parents
        if (map == null) {
            val fresh = ConcurrentReadSafeInt2ObjectMap<Array<AnyUnrollState>>()
            fresh.put(accessor, arrayOf(pred))
            state.parents = fresh
            return
        }

        val existing = map.get(accessor)
        if (existing == null) {
            map.put(accessor, arrayOf(pred))
            return
        }
        for (p in existing) if (p === pred) return
        map.put(accessor, existing + pred)
    }

    /**
     * Drop [pred] from [state]'s incoming edges on [accessor], leaving an EMPTY array behind rather
     * than removing the key -- see [AnyUnrollState.parents] for why a removal is the one map mutation
     * a lock-free reader cannot be made safe against.
     */
    private fun removeParentEdge(state: AnyUnrollState, accessor: AccessorIdx, pred: AnyUnrollState) {
        val map = state.parents ?: return
        val existing = map.get(accessor) ?: return

        var idx = -1
        for (i in existing.indices) {
            if (existing[i] === pred) {
                idx = i
                break
            }
        }
        if (idx < 0) return

        val next = arrayOfNulls<AnyUnrollState>(existing.size - 1)
        System.arraycopy(existing, 0, next, 0, idx)
        System.arraycopy(existing, idx + 1, next, idx, existing.size - idx - 1)
        @Suppress("UNCHECKED_CAST")
        map.put(accessor, next as Array<AnyUnrollState>)
    }

    /**
     * R4/R5: an accessor is read THROUGH an `[any]` whose position is [state]. The BUILD entry point.
     *
     * If the transition already exists it is reused FREE -- that is not an optimisation, it is the
     * termination argument. Otherwise a successor is minted; the pot decides only whether it is
     * `PAID` or `CREDIT`, never whether it exists.
     *
     * **The read never refuses, and that is the whole point.** Refusal leaves the fact holding the
     * state BEFORE the read. That is a correct residual -- the `[any]` branch of `a^-1(SIGMA*.R)` is
     * `SIGMA*.R` itself, which is why refusal is absorption rather than truncation -- but it is lossy
     * in the one dimension the prepend needs: afterwards the fact cannot distinguish "nothing was
     * read here" from "`a` was read here and we declined to pay", so the prepend has nothing to key
     * on. The credit state is the message the read leaves for the prepend.
     *
     * **A `CREDIT` mint is free, and that is deliberate.** The pot is charged only for `PAID` mints,
     * so `total` still stops just past `L` and [budgetExhausted] answers the
     * same question for every existing caller. Charging unpaid mints would make `total` a mixture of
     * two quantities and would shorten the initial-fact abstraction's paid window as a side effect of
     * what `getChild` did.
     *
     * There is no second ceiling and no sink. Two ceilings would have to answer "how much automaton
     * is worth recording for recognition" -- a budget in a different unit from the precision budget
     * `L`, with its own default to defend and its own `0 < 0` edge. One ceiling has no such question,
     * and every value of `L`, `0` included, leaves the mechanism operating.
     */
    fun readChild(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState? {
        if (!enabled || state == null) return state

        if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.reads.incrementAndGet()

        // Fast path: the transition already exists. Lock-free, allocation-free, and by far the
        // common case -- which is the whole reason the automaton exists.
        state.find().children?.get(accessor)?.let {
            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.readsReusedFree.incrementAndGet()
            return it.find()
        }

        synchronized(lock) {
            val current = state.find()
            current.children?.get(accessor)?.let {
                if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.readsReusedFree.incrementAndGet()
                return it.find()
            }

            val dag = current.dag.find()
            val paid = when (kindPolicy) {
                // Rescore mints exactly as PerDag does; it differs only in revisiting the kind
                // afterwards, which is the whole point -- a stamp cannot express "this state later
                // ended up inside a pot four times the limit".
                AnyUnrollKindPolicy.PerDag,
                AnyUnrollKindPolicy.Rescore -> dag.total < limit  // the ONLY thing the pot decides
                AnyUnrollKindPolicy.Global -> globalSpend < limit
                // The CEILING arm. Every rescue strategy for a state that was stamped `PAID` too
                // early -- a global pot, a BFS re-score, anything -- demotes SOME states to `CREDIT`.
                // This demotes all of them, so whatever it fails to buy, none of them can buy either.
                AnyUnrollKindPolicy.AlwaysCredit -> false
            }
            val child = mint(current, accessor, dag, paid)

            if (AnyUnrollDiagnostics.enabled) {
                if (paid) AnyUnrollDiagnostics.paidMints.incrementAndGet()
                else AnyUnrollDiagnostics.creditMints.incrementAndGet()
            }
            return child
        }
    }

    /**
     * The QUERY counterpart of [readChild]: reuse an existing transition, otherwise stay put. Never
     * mints, never charges, never refuses -- a caller that only answers a boolean must not move the
     * budget, and misclassifying a query as a build would trip the cut early and coarsen facts that
     * were never growing.
     */
    fun peekChild(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState? {
        if (!enabled || state == null) return state
        if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.queryReads.incrementAndGet()
        return state.find().children?.get(accessor)?.find() ?: state
    }

    /**
     * EXACTLY the pre-credit contract: reuse free at any pot level, mint only while paid, else null.
     *
     * The initial-fact abstraction needs it, and the reason is a contract detail rather than a
     * preference. Today's read answers a RECORDED transition free, past the limit, BEFORE consulting
     * the pot, and two tests pin that. So moving the abstraction's cut to a `budgetExhausted` test
     * before the read would refuse accessors that are currently granted, silently narrowing the
     * premise side. The split is a second entry point, the same shape the query/build split already
     * uses.
     *
     * It must also never absorb: the abstraction's unroll re-roots the materialised copy and then
     * prepends the accessor it just read, so the backward query would match perfectly, the absorption
     * would fire, and the fold would take the whole prefix away -- throwing away the `filterAccessNode`
     * copy, the most expensive thing in that loop, AFTER paying for the transition.
     */
    fun readChildPaidOnly(state: AnyUnrollState?, accessor: AccessorIdx): AnyUnrollState? {
        if (!enabled || state == null) return state

        if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.reads.incrementAndGet()

        state.find().children?.get(accessor)?.let {
            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.readsReusedFree.incrementAndGet()
            return it.find()
        }

        synchronized(lock) {
            val current = state.find()
            current.children?.get(accessor)?.let {
                if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.readsReusedFree.incrementAndGet()
                return it.find()
            }

            val dag = current.dag.find()
            if (dag.total >= limit) {
                if (AnyUnrollDiagnostics.enabled) {
                    AnyUnrollDiagnostics.readsRefused.incrementAndGet()
                    dag.refusals++
                    AnyUnrollDiagnostics.maxPotRefusals.updateAndGet { maxOf(it, dag.refusals.toLong()) }
                }
                return null
            }

            val child = mint(current, accessor, dag, paid = true)
            child.mintedByUnroll = true
            if (AnyUnrollDiagnostics.enabled) {
                AnyUnrollDiagnostics.paidMints.incrementAndGet()
                AnyUnrollDiagnostics.paidMintsFromUnroll.incrementAndGet()
            }
            return child
        }
    }

    /** The one mint. Caller holds [lock] and has already established there is no transition. */
    private fun mint(
        current: AnyUnrollState,
        accessor: AccessorIdx,
        dag: AnyUnrollDag,
        paid: Boolean,
    ): AnyUnrollState {
        val child = AnyUnrollState(stateIds.incrementAndGet(), dag)
        child.kind = if (paid) AnyUnrollKind.PAID else AnyUnrollKind.CREDIT
        child.pathCount = current.pathCount
        // The `pathCount` words reaching `current` each gain one accessor, so the words reaching
        // `child` are exactly as many and exactly one letter longer apiece.
        child.lengthSum = satAdd(current.lengthSum, current.pathCount, lengthSumCeiling)
        putTransition(current, accessor, child)
        if (paid) {
            // `child.lengthSum` is precisely how much the running SUM-OF-PATH-LENGTHS grows: `child`
            // is new, no other state's contribution moves, so the delta is the whole of its own. The
            // legacy measure charges `current.pathCount` -- how many words appeared, ignoring how
            // long they are -- which bills a forty-accessor chain the same as a first step.
            val charge = if (pathLengthCost) child.lengthSum else current.pathCount
            dag.total = satAdd(dag.total, charge, Int.MAX_VALUE)
            // Charged under the manager lock beside `dag.total`, so a plain Int is enough.
            globalSpend = satAdd(globalSpend, charge, Int.MAX_VALUE)
        }
        if (kindPolicy == AnyUnrollKindPolicy.Rescore && dag.total >= dag.nextRescoreAt) {
            rescoreDag(dag)
        }
        statesMinted.incrementAndGet()
        dag.states++
        noteMaxStates(dag.states)
        noteTotal(dag)

        if (AnyUnrollDiagnostics.enabled) {
            AnyUnrollDiagnostics.recordPot(dag.total)
            AnyUnrollDiagnostics.transitionsCreated.incrementAndGet()
        }
        return child
    }

    /**
     * Whether a covered accessor may still be WRITTEN above an `[any]` sitting at [state].
     *
     * Deliberately NOT [budgetExhausted]: that is a property of the pot, shared by every `[any]`
     * descended from one origin, and it cannot tell a step the callee genuinely produced from a step
     * this `[any]` sold.
     */
    /** The kind of an `[any]` position, for diagnostics that need to say WHY a write was written. */
    fun kindOf(state: AnyUnrollState?): AnyUnrollKind? =
        if (!enabled || state == null) null else state.find().kind

    /**
     * @param count whether this call is a real prepend and should be weighed. The one caller that
     *   passes `false` is a diagnostic probe that runs only when `anyManagerDiag` is on; letting it
     *   weigh would make the measurement flag change the ordering, the demotions and the findings.
     */
    fun writesAbove(state: AnyUnrollState?, count: Boolean = true): Boolean {
        if (!enabled || state == null) return true
        val current = state.find()
        if (count) {
            // One read, so the guard cannot be invalidated between the test and the increment: a
            // torn guard would wrap to Int.MIN_VALUE and sort a hot state to the FRONT of the budget.
            val seen = current.traffic
            if (seen in 0 until Int.MAX_VALUE) current.traffic = seen + 1
        }
        val kind = current.kind
        return kind == AnyUnrollKind.ORIGIN || kind == AnyUnrollKind.PAID
    }

    /**
     * The BACKWARD step: the position to move to when [accessor] is absorbed into an `[any]` sitting
     * at [state], or `null` when it is not an incoming edge at all.
     *
     * **Null rather than the position itself, and that is load-bearing.** A caller testing
     * `result === state` to mean "not from this `[any]`" would conflate two opposite situations: on a
     * SELF-LOOP `p --a--> p` the correct answer is `p` -- absorb, staying put -- while the identity
     * test reads it as "no incoming edge" and WRITES the accessor, precisely where the automaton says
     * the accessor is already folded in. `createAnyEdge`'s `union(installed, found)` manufactures such
     * loops itself, joining an installed state with states collected from the subtree below it.
     *
     * Nothing depends on this naming the ONE true predecessor -- absorption is correct at any state,
     * because the state does not enter the DENOTATION of an `[any]` edge. `[any]@r` is `SIGMA*` for
     * every `r`; the state is a budget and provenance annotation, and every consumer that branches on
     * it (`writesAbove`, `readChildPaidOnly`, `budgetExhausted`) is sound in BOTH branches. So the
     * pick is a precision decision, never a soundness one.
     *
     * What it must be is REPRODUCIBLE, hence the total order below. It is NOT complete -- the set is
     * enumerated and one member returned -- and design §5.8(b) is right that no tie-break can make it
     * complete, because the backward run needs the rest of the word before it can choose. `§5.8` was
     * measured and retired; see the results document for why that measurement bounded only the
     * completeness half.
     *
     * **The order is ranked, not arbitrary** (2026-08-26), and the rank has exactly one level:
     *
     * 1. **a self-loop**, if one is a candidate. `p --a--> p` says `a` is ALREADY folded into this
     *    `[any]`, so staying is the exact inverse of the read that put the fact here -- the fixpoint
     *    condition, taken whenever it is on offer, instead of by whether its id happened to be low.
     * 2. **min id**, unchanged, as the reproducible tie-break.
     *
     * A rank on "stay inside this pot" was considered and is NOT here, because it would be dead
     * code: `mint` gives a child its parent's dag and only `union` fuses dags, so a state's dag is
     * its reachability component and every candidate is inside it already. The greedy pick was never
     * able to jump automata -- which retires, structurally, the sharpest harm one could attribute
     * to it.
     *
     * This changes only WHERE a fork lands, never WHETHER it absorbs, so `absorptions` is unaffected
     * by construction; the counters say how often the distinction could have mattered at all.
     */
    fun absorbInto(state: AnyUnrollState, accessor: AccessorIdx, count: Boolean = true): AnyUnrollState? {
        if (!enabled) return null

        val current = state.find()
        val preds = current.parents?.get(accessor) ?: return null

        var best: AnyUnrollState? = null
        var bestRank = Int.MAX_VALUE
        var hits = 0
        var selfLoop = false
        var firstKind: AnyUnrollKind? = null
        var kindSplit = false
        var minId: AnyUnrollState? = null

        for (raw in preds) {
            val pred = raw.find()

            // Lemma 9.2's forward re-check. `mergeStates`'s conflict arm queues a pair for merging
            // rather than writing the transition, so between that queueing and the drain of
            // `pending` a lock-free scan can observe a predecessor whose forward edge does not yet
            // resolve back. This turns that window into a MISS rather than a wrong predecessor.
            // It must stay AHEAD of the ranking, or a predecessor inside that window could outrank
            // a real one.
            if (pred.children?.get(accessor)?.find() !== current) {
                if (count && AnyUnrollDiagnostics.enabled) {
                    AnyUnrollDiagnostics.witnessForwardCheckFailed.incrementAndGet()
                }
                continue
            }

            hits++
            val rank = if (pred === current) { selfLoop = true; 0 } else 1

            if (best == null || rank < bestRank || (rank == bestRank && pred.id < best.id)) {
                best = pred
                bestRank = rank
            }

            if (count && AnyUnrollDiagnostics.enabled) {
                val k = pred.kind
                if (firstKind == null) firstKind = k else if (firstKind != k) kindSplit = true
                if (minId == null || pred.id < minId.id) minId = pred
            }
        }

        if (count && AnyUnrollDiagnostics.enabled && hits > 1) {
            AnyUnrollDiagnostics.absorbForkHits.incrementAndGet()
            AnyUnrollDiagnostics.recordFork(hits)
            // Design §5.8's benefit B, measured for the first time -- see [absorbForkKindSplit] for
            // why the kind is the only thing the choice can move.
            if (kindSplit) AnyUnrollDiagnostics.absorbForkKindSplit.incrementAndGet()
            if (selfLoop) AnyUnrollDiagnostics.absorbForkSelfLoopPreferred.incrementAndGet()
            if (minId !== best) AnyUnrollDiagnostics.absorbForkChoiceChanged.incrementAndGet()
        }
        return best
    }

    /** Whether the pot behind [state] is spent, i.e. whether an accessor may still be written above it. */
    fun budgetExhausted(state: AnyUnrollState?): Boolean {
        if (!enabled || state == null) return false
        return state.find().dag.find().total >= limit
    }

    /** For tests and diagnostics only. */
    fun totalOf(state: AnyUnrollState): Int = state.find().dag.find().total

    /**
     * Latch the exhaustion TRANSITION. Called under [lock], wherever [AnyUnrollDag.total] is written.
     *
     * `total` is monotone and the latch is never cleared, so nothing drifts downward except at the
     * fusion, where the decrement is exactly the dag that ceased to exist.
     */
    private fun noteTotal(dag: AnyUnrollDag) {
        if (!dag.exhaustedCounted && dag.total >= limit) {
            dag.exhaustedCounted = true
            dagsExhausted.incrementAndGet()
        }
    }

    private fun noteMaxStates(candidate: Int) {
        var cur = maxStatesPerDag.get()
        while (candidate > cur && !maxStatesPerDag.compareAndSet(cur, candidate)) cur = maxStatesPerDag.get()
    }

    /**
     * The `[any]` line of the periodic progress report, or `null` when the feature is off.
     *
     * What it is for is separating failure modes the aggregates cannot:
     *
     * | reading | means | lever |
     * |---|---|---|
     * | `live` large, `beyond` ~ 0 | origins proliferating, none spending | the mint sites, not `L` |
     * | `live` small, `beyond` ~ `live` | a few origins absorbing the whole program | `L`, or that origin |
     * | `beyond` climbing while `(+delta)` falls | the cut fires and the work MOVES | the L=100 shape |
     *
     * `live` honestly means live REPRESENTATIVES, not dags still reachable from a live fact: a pot
     * whose facts have all been dropped still counts. Making it mean the latter needs the weak
     * registry this design refuses, so the counter over-reports by exactly the un-reclaimed amount.
     */
    fun liveReport(): String? {
        if (!enabled) return null
        val s = liveStats()

        // An invariant of the scheme, not a defensive check: a violation means the fusion accounting
        // is wrong, which is otherwise a silent, slowly drifting number that would be believed.
        // `beyond > live` IS an alarm -- it is an invariant of the counting scheme, and a violation
        // means the fusion accounting is wrong, which is otherwise a silent, slowly drifting number
        // that would be believed. `remapDeferred` is NOT: it is a magnitude, reported so the drain
        // window stays visible rather than assumed away.
        val alarm = if (s.beyond > s.liveRoots) " INCONSISTENT(beyond>live)" else ""

        return "[any] roots: ${s.liveRoots} live, ${s.beyond} beyond, ${s.states} states " +
            "(max/dag ${s.maxStatesPerDag}), transitions ${s.transitions}, " +
            "remapDeferred ${remapConflicts.get()}" + alarm
    }

    /** The same numbers unformatted, so a test can assert the fusion accounting rather than a string. */
    fun liveStats(): AnyUnrollLiveStats = AnyUnrollLiveStats(
        liveRoots = dagsCreated.get() - dagsFused.get(),
        beyond = dagsExhausted.get(),
        states = statesMinted.get() - statesMerged.get(),
        maxStatesPerDag = maxStatesPerDag.get(),
        transitions = transitionsInstalled.get(),
    )

    private fun satAdd(a: Int, b: Int, ceiling: Int): Int {
        val sum = a.toLong() + b.toLong()
        return if (sum >= ceiling) ceiling else sum.toInt()
    }

    companion object {
        const val ANY_UNROLL_LIMIT_PROPERTY = "opentaint.anyUnrollLimit"

        /**
         * `-Dopentaint.anyUnrollLimit=<n>`: `L`, the per-origin budget.
         *
         * `n < 0` -- the default -- means the manager is off entirely: no state is allocated, no
         * `AccessNode` carries an id, nothing is recorded and nothing is refused, so the analysis is
         * bit-identical to one built without the feature. A non-negative `n` lets each `[any]` ORIGIN
         * materialise a path-weighted total of `n` concrete accessors before it starts absorbing
         * further steps instead of writing them.
         *
         * Read once, at class initialisation: it is consulted per covered read.
         */
        val DEFAULT_ANY_UNROLL_LIMIT: Int =
            System.getProperty(ANY_UNROLL_LIMIT_PROPERTY)?.trim()?.toIntOrNull() ?: -1

        const val ANY_UNROLL_PATH_LENGTH_COST_PROPERTY = "opentaint.anyPathLengthCost"

        /**
         * `-Dopentaint.anyPathLengthCost=true|false`, default `true`: what `L` is a budget OF.
         *
         * `true` -- the pot spends the SUM OF THE LENGTHS of the accessor sequences it has
         * materialised, so `L = 100` buys a hundred accessors however they are arranged: one chain of
         * a hundred, or a hundred first steps, or anything between.
         *
         * `false` -- the pre-2026-08-27 measure, one unit per sequence regardless of length, which
         * charges a hundred-accessor chain the same 1 as a single step off the origin. It is retained
         * as an ablation, not as a supported mode: with it the printed `total` is a count of words
         * and cannot be compared against a `total` printed by the default.
         *
         * The two are the same number exactly when every sequence has length 1, i.e. for a pot that
         * only ever took first steps.
         */
        val DEFAULT_PATH_LENGTH_COST: Boolean =
            System.getProperty(ANY_UNROLL_PATH_LENGTH_COST_PROPERTY)?.trim()
                ?.toBooleanStrictOrNull() ?: true

        const val ANY_UNROLL_KIND_MERGE_PROPERTY = "opentaint.anyUnrollKindMerge"

        /**
         * `-Dopentaint.anyUnrollKindMerge=below|beyond`, default `below`.
         *
         * Parsed null-returning and STRICTLY, matching `toBooleanStrictOrNull` / `toIntOrNull` at the
         * knob above, so a typo falls back to the default. A bare `enumValueOf` would turn a
         * misspelled `-D` into a class-initialisation failure -- and for a knob read at class-init
         * that means the analyzer does not start. This is the module's first enum-valued knob, so it
         * sets the precedent.
         */
        val DEFAULT_KIND_MERGE: AnyUnrollKindMerge =
            System.getProperty(ANY_UNROLL_KIND_MERGE_PROPERTY)?.trim()?.let { raw ->
                AnyUnrollKindMerge.entries.firstOrNull { it.name.equals(raw, ignoreCase = true) }
                    ?: AnyUnrollKindMerge.entries.firstOrNull {
                        it.name.removePrefix("Prefer").equals(raw, ignoreCase = true)
                    }
            } ?: AnyUnrollKindMerge.PreferBelow

        const val ANY_UNROLL_KIND_POLICY_PROPERTY = "opentaint.anyUnrollKindPolicy"

        /** `-Dopentaint.anyUnrollKindPolicy=perDag|global`, default `perDag`. Parsed as above. */
        val DEFAULT_KIND_POLICY: AnyUnrollKindPolicy =
            System.getProperty(ANY_UNROLL_KIND_POLICY_PROPERTY)?.trim()?.let { raw ->
                AnyUnrollKindPolicy.entries.firstOrNull { it.name.equals(raw, ignoreCase = true) }
            } ?: AnyUnrollKindPolicy.PerDag

        const val ANY_UNROLL_RESCORE_STRATEGY_PROPERTY = "opentaint.anyUnrollRescoreStrategy"

        /** `-Dopentaint.anyUnrollRescoreStrategy=bfs|population`, default `bfs`. Parsed as above. */
        val DEFAULT_RESCORE_STRATEGY: AnyUnrollRescoreStrategy =
            System.getProperty(ANY_UNROLL_RESCORE_STRATEGY_PROPERTY)?.trim()?.let { raw ->
                AnyUnrollRescoreStrategy.entries.firstOrNull { it.name.equals(raw, ignoreCase = true) }
            } ?: AnyUnrollRescoreStrategy.Bfs

        // Mint sites, for §12.1(a): "distinct managers per origin, BY ALLOCATING SITE". The count
        // alone does not say which site leaked.
        const val MINT_PREPEND = 0
        const val MINT_DESERIALIZE = 1

        /**
         * The raw single-edge `create`, shared by the `filterStartsWith` spine fold,
         * `reconstructRemainder` and both premise chain folds.
         *
         * They are deliberately ONE bucket rather than four: they all reach the same choke point
         * with a state their caller supplied, so a mint here means some caller failed to supply one,
         * and the useful signal is "any of them leaked" rather than which. An earlier split had a
         * `spineRebuild` bucket that was structurally unreachable and therefore always read zero,
         * which is worse than no bucket at all.
         */
        const val MINT_RAW_EDGE = 2
        const val MINT_BULK_MERGE = 3
        const val MINT_TEST = 4
        const val MINT_SITE_COUNT = 5

        val MINT_SITE_NAMES = arrayOf(
            "prepend", "deserialize", "rawEdge", "bulkMerge", "test"
        )
    }
}

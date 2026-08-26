package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet.Empty
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.ReversedApNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.createNodeFromReversedAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.foldRight
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.create
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromReversedAp
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isAlwaysUnrollNext
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode as AccessTreeNode

/**
 * Turns a concrete taint fact into premises, WITHOUT ever unrolling an `[any]`.
 *
 * Design: `docs/superpowers/specs/2026-08-26-tifa-never-unroll-design.md`. At a walk state
 * `(T, N, p)` -- trie node, fact node, prefix -- with `E = T.exclusions()`:
 *
 *  - **R0** `E == null` -- nothing has ever terminated here, so hand out `p`; `p.*` covers the rest.
 *  - **R1** no accessor is ever materialised out of an `[any]` into `added`. That is the change.
 *  - **R2** for each `a` the fact holds LITERALLY: descend if `T.child(a)` exists, else emit `p.a`
 *    if `a in E`.
 *  - **R3a** the covered frontier: one `[any]` edge for everything `[any]` denotes.
 *  - **R3b** the uncovered frontier: `[any]` covers field and element steps only, so a taint mark
 *    below one is NOT denoted by `p.[any]` and has to be named -- twice, once for each reading of
 *    the zero-or-more.
 *  - **R3c** demanded, covered, absent: emit `p.a` without materialising `a` anywhere. This is what
 *    the automata backend has always done (`AutomataInitialFactAbstraction.abstractGraph`).
 *  - **R4** the virtual descent: read `N.getChild(a)` rather than storing what the unroll copied.
 *
 * The unroll's real job was never precision -- it was putting a literal child into `added` so that a
 * later walk's `forEachAccessor` would route to the deeper trie node. R3c hands out the premise,
 * which registers the trie node; R4 is what makes the next walk descend there. The cost the unroll
 * carried was the COPY (`carrierPerRequest = 10.72` nodes, of which 99.4% still owned an `[any]` and
 * so re-armed the next round); R4 walks the same shapes and stores none of them.
 */
class TreeInitialFactAbstraction(
    private val apManager: TreeApManager,
    methodInitialStatement: CommonInst? = null,
): InitialFactAbstraction {
    private val methodLabel: String? =
        if (TifaDiagnostics.enabled) methodInitialStatement?.location?.method?.toString() else null

    private fun baseStats(base: AccessPathBase): BaseStats? =
        methodLabel?.let { TifaDiagnostics.baseStats("$base @ $it") }

    private val initialFacts = MethodSameMarkInitialFact(apManager, hashMapOf())
    private val interner = AccessTreeSoftInterner(apManager)

    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as AccessTree

        if (TifaDiagnostics.enabled) {
            TifaDiagnostics.addCalls.incrementAndGet()
            baseStats(factAp.base)?.addCalls?.incrementAndGet()
        }

        // note: we can ignore fact exclusions here
        val facts = initialFacts.getOrPut(factAp.base)
        val stats = baseStats(factAp.base)
        val addedFact = facts.addInitialFact(factAp.access, interner, stats) ?: return emptyList()

        if (TifaDiagnostics.enabled) {
            TifaDiagnostics.addDeltas.incrementAndGet()
            stats?.recordAdded(facts.allAddedFacts())
        }

        val abstractFacts = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        addAbstractInitialFact(facts, factAp.base, addedFact, abstractFacts, typeChecker)
        return abstractFacts
    }

    override fun registerNewInitialFact(
        factAp: InitialFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        factAp as AccessPath

        val facts = initialFacts.getOrPut(factAp.base)

        val excludedAccessors = IntOpenHashSet()
        when (val ex = factAp.exclusions) {
            is ExclusionSet.Concrete -> ex.set.forEach {
                with(apManager) { excludedAccessors.add(it.idx) }
            }
            Empty -> {
                // do nothing
            }
            ExclusionSet.Universe -> error("Unexpected universe exclusion")
        }

        if (!facts.addAnalyzedInitialFact(factAp.access, excludedAccessors)) return emptyList()

        val abstractFacts = mutableListOf<Pair<InitialFactAp, FinalFactAp>>()
        addAbstractInitialFact(facts, factAp.base, facts.allAddedFacts(), abstractFacts, typeChecker)
        return abstractFacts
    }

    private fun addAbstractInitialFact(
        facts: MethodSameBaseInitialFact,
        concreteFactBase: AccessPathBase,
        initialConcreteFact: AccessTreeNode,
        abstractFacts: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        typeChecker: FactTypeChecker
    ) {
        // The ladder, and the only loop left.
        //
        // A premise REGISTERS ITSELF at the emission site, so handing out `p` creates `p`'s trie
        // path and the next walk descends past it instead of stopping there. One walk therefore
        // climbs exactly one rung, and a demand registered `k` links down needs `k` walks. The old
        // code got those extra walks for free from the unroll's round loop -- a round materialised a
        // delta and the delta was walked again. With nothing materialised, the loop has to be driven
        // by the only thing that still changes between rounds: whether the round registered a
        // premise the trie did not already hold.
        //
        // It terminates, and the argument is not about fact shape. Every emission registers with an
        // EMPTY exclusion set, so a trie node the walk itself created can never satisfy R3a
        // (`E != {}`), R3c (`a in E`) or R2's emit arm. Only nodes registered from OUTSIDE, by
        // `registerNewInitialFact`, carry demand, and the rounds are bounded by the depth of that
        // externally registered trie.
        var round = 0
        while (true) {
            var registeredNew = false
            val firstRound = round == 0

            abstractAccessPath(facts.analyzed, initialConcreteFact, typeChecker) { abstractAccess, governingAnyId ->
                apManager.cancellation.checkpoint()

                if (TifaDiagnostics.enabled) {
                    TifaDiagnostics.emits.incrementAndGet()
                    val stats = baseStats(concreteFactBase)
                    stats?.emits?.incrementAndGet()

                    // Two different claims about the `[any]`, and they come apart on this workload.
                    // `governingAnyId != null` means the walk reached this position BY crossing an
                    // `[any]`; the chain check means the `[any]` is still in what gets stored.
                    if (governingAnyId != null) {
                        TifaDiagnostics.emitsUnderAny.incrementAndGet()
                        stats?.emitsUnderAny?.incrementAndGet()
                    }
                    var chainNode = abstractAccess
                    var chainCarriesAny = false
                    while (chainNode != null) {
                        if (chainNode.accessor == ANY_ACCESSOR_IDX) {
                            chainCarriesAny = true
                            break
                        }
                        chainNode = chainNode.prev
                    }
                    if (chainCarriesAny) {
                        TifaDiagnostics.emitsWithAnyInChain.incrementAndGet()
                        stats?.emitsWithAnyInChain?.incrementAndGet()
                    }
                }

                val initialAbstractAccessNode = apManager.createNodeFromReversedAp(abstractAccess)
                val initialAbstractAp = AccessPath(apManager, concreteFactBase, initialAbstractAccessNode, Empty)

                // The emitted fact INHERITS the walk's governing state rather than minting one.
                // Minting per emission would restore a per-premise budget -- finer than the
                // per-`(entry point, base)` counter this replaces, and wrong the same way. The
                // predecessor exists and the walk is holding it: the `[any]` in the emitted chain is
                // not invented, it is the `[any]` edge the walk crossed.
                val apAccess = apManager.createAbstractNodeFromReversedAp(abstractAccess, governingAnyId)
                val ap = AccessTree(apManager, concreteFactBase, apAccess, Empty)

                val registered = facts.addAnalyzedInitialFact(initialAbstractAccessNode, exclusions = IntOpenHashSet())
                if (registered) registeredNew = true

                // Round 0 reproduces the old contract exactly: everything the walk reaches is handed
                // out, whether or not the trie already held it. Later rounds exist only to climb, so
                // they contribute only what the trie did not have -- otherwise a chain below an
                // always-unroll-next accessor, which no trie test gates, would be re-emitted once
                // per round.
                if (firstRound || registered) abstractFacts.add(initialAbstractAp to ap)
            }

            round++
            if (!registeredNew || SINGLE_ROUND) break
            if (TifaDiagnostics.enabled) TifaDiagnostics.walkRounds.incrementAndGet()
        }
    }

    private fun ReversedApNode?.createFilter(typeChecker: FactTypeChecker): FactTypeChecker.FactApFilter {
        val accessors = mutableListOf<Accessor>()
        foldRight(Unit) { accessor, _ ->
            with(apManager) {
                accessors.add(accessor.accessor)
            }
        }
        return typeChecker.accessPathFilter(accessors.asReversed())
    }

    /**
     * `U` -- the accessors an `[any]` does NOT cover, so the ones a `p.[any]` premise cannot stand in
     * for. Taint marks, `[final]`, `[value]`, type-info accessors, class statics, and any field the
     * strategy declines to unroll.
     *
     * The order of the three tests is load-bearing, not cosmetic.
     * [AnyAccessorUnrollStrategy.AnyAccessorDisabled], installed for the whole prescan, does not
     * return `false` from `unrollAccessor` -- it THROWS -- and several test strategies throw on
     * `ValueAccessor` specifically. Every accessor that would provoke that is decided by
     * [isAlwaysUnrollNext] or [isStaticAccessor] first, and no covered accessor is
     * always-unroll-next, so the short circuit is exact rather than approximate.
     */
    private fun AccessorIdx.isUncoveredByAny(): Boolean =
        isAlwaysUnrollNext() || isStaticAccessor() || !apManager.isCoveredByAny(this)

    data class AbstractionState(
        val analyzedTrieRoot: AccessPathTrieNode,
        val added: AccessTreeNode,
        val currentAp: ReversedApNode?,
        /**
         * The `[any]` manager state the walk is under, or null above every `[any]`.
         *
         * One reference per walk state and no set, because the branch invariant guarantees a walk
         * down one path meets exactly one manager. It travels on the FACT side only -- the emitted
         * `AccessPath` gets nothing, and that matters more than it looks: premise identity keys the
         * whole demand system, and two premises differing only by an annotation would be two
         * demands.
         */
        val governingAnyId: AnyUnrollState?,
    )

    private inline fun abstractAccessPath(
        initialAnalyzedTrieRoot: AccessPathTrieNode,
        initialAdded: AccessTreeNode,
        typeChecker: FactTypeChecker,
        crossinline createAbstractAp: (ReversedApNode?, AnyUnrollState?) -> Unit
    ) {
        val unprocessed = mutableListOf<AbstractionState>()
        unprocessed.add(AbstractionState(initialAnalyzedTrieRoot, initialAdded, currentAp = null, governingAnyId = null))

        while (unprocessed.isNotEmpty()) {
            val state = unprocessed.removeLast()

            if (TifaDiagnostics.enabled) TifaDiagnostics.walkStates.incrementAndGet()

            val trie = state.analyzedTrieRoot
            val added = state.added

            // R0. No premise has ever terminated here, so `p` itself is the answer and its `.*`
            // covers everything below. Emitting it is also what primes this level for the next walk.
            val exclusions = trie.exclusions()
            if (exclusions == null) {
                createAbstractAp(state.currentAp, state.governingAnyId)
                continue
            }

            val anyBranch = if (added.containsAnyAccessor()) added.getChild(ANY_ACCESSOR_IDX) else null
            if (anyBranch != null) {
                if (TifaDiagnostics.enabled) TifaDiagnostics.anyDescents.incrementAndGet()

                val anyAp = ReversedApNode(ANY_ACCESSOR_IDX, state.currentAp)
                // The premise emitted below this point NAMES the `[any]`, so it is governed by the
                // state of the edge just crossed.
                val anyGoverning = added.anyId ?: state.governingAnyId
                val anyTrie = trie.child(ANY_ACCESSOR_IDX)

                // R3a -- the covered frontier, one edge for everything `[any]` denotes.
                //
                // The `E != {}` guard is what keeps the 19 `expectedEmpty` scenarios green: a level
                // that has handed out a premise and been asked nothing of it is already covered by
                // that premise's `.*`, and a coarse edge there would be pure volume.
                //
                // The emission arm is OFF by default -- see [ANY_FRONTIER_PREMISE], which overturns
                // design §7 R5 on evidence. The DESCENT arm is not gated: an `[any]` trie child
                // exists only because the engine registered a premise there, and walking on to
                // answer it is the ordinary demand-driven behaviour.
                if (anyTrie != null) {
                    unprocessed += AbstractionState(anyTrie, anyBranch, anyAp, anyGoverning)
                } else if (apManager.anyFrontierPremise && exclusions.isNotEmpty()) {
                    if (TifaDiagnostics.enabled) TifaDiagnostics.emitsAnyFrontier.incrementAndGet()
                    createAbstractAp(anyAp, anyGoverning)
                }

                // R3b -- the uncovered frontier, at THIS prefix.
                //
                // `[any]` is zero-or-more steps over FIELD and ELEMENT, so a taint mark below one is
                // not something `p.[any]` denotes -- and the mark is the finding. `[any]` being
                // zero-or-more is also what makes `p.u` the right premise for it: a sink
                // precondition `<this>.![m].$` sits at `root -> mark` in the trie, and a fact
                // `this.[any].![m].$` has no mark child of its own, so the demand is reachable only
                // from here. `AccessTree.getChild` hoists the `[any]`'s child up, so `p.u` matches
                // the fact that produced it.
                //
                // MEASURED, not assumed: with this block off, `CleanerFieldSensitivityAnalysisTest`
                // loses two `the unsanitized field reports` cases outright, which is the unit-scale
                // version of the `ssrf` and `path-traversal` losses the earlier prototypes took on
                // conductor. That is what SUPPRESS_UNCOVERED_FRONTIER reproduces on demand.
                //
                // What is NOT here: a proactive `p.[any].u`, i.e. the same mark named one link below
                // the `[any]` off the demand registered at `p`. It looks like the missing half of a
                // zero-or-more, and the design asked for it, but it is the one shape that resurrects
                // a cleaned field -- `TreeCleanerFieldSensitivityAnalysisTest.concrete two-level
                // clean over an abstract source`, red with it and green without. A `p.[any].u` entry
                // fact cannot express a node deletion INSIDE the `[any]`, so a cleaner that bites on
                // a concrete path stops biting under it, and the premise is a pure false positive
                // generator. The `[any]`-carrying member of the family is still reachable, but only
                // where the engine has actually refined `p.[any]` itself: that demand lands on
                // `anyTrie` and the R3a descent below answers it through the ordinary per-accessor
                // helper. Demand-driven, not speculative -- which is the rule the rest of this file
                // follows.
                if (!SUPPRESS_UNCOVERED_FRONTIER) {
                    anyBranch.forEachAccessor { accessor, node ->
                        if (accessor == ANY_ACCESSOR_IDX) return@forEachAccessor
                        if (!accessor.isUncoveredByAny()) return@forEachAccessor

                        if (TifaDiagnostics.enabled) TifaDiagnostics.emitsUncoveredFrontier.incrementAndGet()
                        abstractAccessPath(
                            trie, accessor, node, state.currentAp, state.governingAnyId,
                            unprocessed, createAbstractAp,
                        )
                    }
                }

                // R3c -- demanded, covered, and present in NO concrete branch of the fact.
                //
                // The premise is handed out without materialising the accessor anywhere. Eight
                // scenarios in the cross-backend `InitialFactAbstractionTest` assert exactly this
                // shape, and the automata backend has always answered them this way
                // (`AutomataInitialFactAbstraction.abstractGraph`, the `startsWith(anyAccessorIdx)`
                // arm) with no round loop and no memo. The tree backend's mechanism was the unroll;
                // R1 removes it and this is the replacement.
                var accessorFilter: FactTypeChecker.FactApFilter? = null
                if (!SUPPRESS_SYNTHESISED) exclusions.forEachInt { accessor ->
                    // A trie child means the premise is already out; R2 or R4 descends into it.
                    if (trie.child(accessor) != null) return@forEachInt
                    // Held literally: R2 owns it, and emits exactly the same premise.
                    if (added.hasLiteralChild(accessor)) return@forEachInt
                    if (accessor.isUncoveredByAny()) return@forEachInt

                    val filter = accessorFilter
                        ?: state.currentAp.createFilter(typeChecker).also { accessorFilter = it }
                    when (filter.check(with(apManager) { accessor.accessor })) {
                        is FactTypeChecker.FilterResult.Accept,
                        is FactTypeChecker.FilterResult.FilterNext -> {
                            // accept
                        }

                        is FactTypeChecker.FilterResult.Reject -> return@forEachInt
                    }

                    if (TifaDiagnostics.enabled) TifaDiagnostics.emitsSynthesised.incrementAndGet()
                    createAbstractAp(ReversedApNode(accessor, state.currentAp), state.governingAnyId)
                }
            }

            // R2 -- what the fact holds literally.
            state.added.forEachAccessor { accessor, node ->
                // `[any]` is owned by the block above, which sees the same child through `getChild`.
                if (accessor == ANY_ACCESSOR_IDX) return@forEachAccessor

                abstractAccessPath(
                    trie, accessor, node, state.currentAp, state.governingAnyId,
                    unprocessed, createAbstractAp,
                )
            }

            // R4 -- the virtual descent, and the reason R3c is enough on its own.
            //
            // Emitting `p.a` registers `T.child(a)` but materialises nothing, so without this the
            // abstraction sticks one level below every `[any]` forever: no later walk is ever routed
            // to trie node `a`. `AccessNode.getChild` is documented as the unique point at which a
            // concrete accessor is SYNTHESISED out of an `[any]` -- for a node owning one it returns
            // the merge of the literal `a` child, the `[any]` subtree's `a` child, and the `[any]`
            // re-installed below. That is exactly the node the unroll built by copying the carrier.
            //
            // It reads through `getChild`, not `getChildRecording`: recording a transition per
            // ladder step would put the walk back inside the `[any]` manager's budget, which is the
            // coupling R1 exists to remove. A read cannot grow a stored fact -- the result is
            // assembled from subtrees of the receiver and nothing is merged back into `added`.
            if (anyBranch != null && !SUPPRESS_VIRTUAL_DESCENT) {
                trie.forEachChild { accessor, childTrie ->
                    if (accessor == ANY_ACCESSOR_IDX) return@forEachChild
                    // R2 already descended into it.
                    if (added.hasLiteralChild(accessor)) return@forEachChild
                    // Only a covered accessor can be reached THROUGH the `[any]`; an uncovered one
                    // under it is R3b's, at this prefix rather than one link deeper.
                    if (accessor.isUncoveredByAny()) return@forEachChild

                    val child = added.getChild(accessor) ?: return@forEachChild
                    if (TifaDiagnostics.enabled) TifaDiagnostics.virtualDescents.incrementAndGet()
                    unprocessed += AbstractionState(
                        childTrie, child, ReversedApNode(accessor, state.currentAp), state.governingAnyId,
                    )
                }
            }
        }
    }

    private inline fun abstractAccessPath(
        analyzedTrieRoot: AccessPathTrieNode,
        accessor: AccessorIdx,
        addedNode: AccessTreeNode,
        currentAp: ReversedApNode?,
        governingAnyId: AnyUnrollState?,
        unprocessed: MutableList<AbstractionState>,
        crossinline createAbstractAp: (ReversedApNode?, AnyUnrollState?) -> Unit
    ) {
        val node = analyzedTrieRoot.child(accessor)
        if (node != null) {
            val apWithAccessor = ReversedApNode(accessor, currentAp)
            if (accessor.isAlwaysUnrollNext()) {
                abstractNextAccessPath(addedNode, apWithAccessor, governingAnyId) { ap, governing ->
                    createAbstractAp(ap, governing)
                }
            } else {
                unprocessed += AbstractionState(node, addedNode, apWithAccessor, governingAnyId)
            }
            return
        }

        val exclusions = analyzedTrieRoot.exclusions()

        // We have no excludes -> continue with the most abstract fact
        if (exclusions == null) {
            createAbstractAp(currentAp, governingAnyId)
            return
        }

        // Concrete: a.b.* E
        // Added: a.* S
        if (!exclusions.contains(accessor)) {
            // We have no conflict with added facts
            return
        }

        // We have initial fact that exclude {b} and we have no a.b fact yet
        if (!accessor.isAlwaysUnrollNext()) {
            // Return a.b.* {}
            createAbstractAp(ReversedApNode(accessor, currentAp), governingAnyId)
            return
        }

        val apWithAccessor = ReversedApNode(accessor, currentAp)
        abstractNextAccessPath(addedNode, apWithAccessor, governingAnyId) { ap, governing ->
            createAbstractAp(ap, governing)
        }
    }

    /**
     * The continuation below an always-unroll-next accessor (a taint mark, `[final]`, `[value]`, a
     * type-info accessor). There is no trie and no demand test here: a premise may not stop at such
     * an accessor, so every branch below it is emitted, and the recursion runs until it reaches one
     * that a premise may stop at.
     *
     * `[any]` needs no case of its own. It is not always-unroll-next, so the loop below emits
     * `currentAp.[any]` and stops -- an ordinary accessor, the same shape [abstractAccessPath]
     * emits, and its `.*` completion covers the whole subtree the `[any]` carried.
     *
     * The reachable shapes are `[any]` under `[value]` or under a type-info accessor. `[any]` under a
     * taint mark is unconstructible -- `AccessTree.AccessNode.create` bans a mark above a structured
     * node -- which is also what keeps the emitted chain legal: `createAbstractNodeFromReversedAp`
     * would otherwise have to build a mark above an `[any]` node and would fail that same check.
     */
    private fun abstractNextAccessPath(
        addedNode: AccessTreeNode,
        currentAp: ReversedApNode,
        governingAnyId: AnyUnrollState?,
        createAbstractAp: (ReversedApNode, AnyUnrollState?) -> Unit
    ) {
        if (addedNode.isFinal) {
            createAbstractAp(ReversedApNode(FINAL_ACCESSOR_IDX, currentAp), governingAnyId)
        }

        addedNode.forEachAccessor { accessor, node ->
            val nextAp = ReversedApNode(accessor, currentAp)
            val nextGoverning =
                if (accessor == ANY_ACCESSOR_IDX) addedNode.anyId ?: governingAnyId else governingAnyId
            if (!accessor.isAlwaysUnrollNext()) {
                createAbstractAp(nextAp, nextGoverning)
            } else {
                abstractNextAccessPath(node, nextAp, nextGoverning, createAbstractAp)
            }
        }
    }

    private class MethodSameMarkInitialFact(
        val manager: TreeApManager,
        val facts: MutableMap<AccessPathBase, MethodSameBaseInitialFact>
    ) {
        fun getOrPut(base: AccessPathBase): MethodSameBaseInitialFact = facts.getOrPut(base) {
            MethodSameBaseInitialFact(manager, added = null, AccessPathTrieNode.empty())
        }
    }

    private class MethodSameBaseInitialFact(
        val manager: TreeApManager,
        private var added: AccessTreeNode?,
        val analyzed: AccessPathTrieNode
    ) {
        fun allAddedFacts(): AccessTreeNode = added ?: manager.create()

        fun addInitialFact(
            ap: AccessTreeNode,
            interner: AccessTreeSoftInterner,
            stats: BaseStats? = null,
        ): AccessTreeNode? {
            val currentNode = added ?: manager.create()

            // The `[any]` subsumption the merge performs everywhere else is switched OFF here --
            // `foldToAny = false` appears at exactly two sites in this module and both are in this
            // class. This is the accumulator that grows, and it is the one tree where an `[any]` and
            // the concrete enumerations it already denotes sit side by side. The probe measures what
            // the trim WOULD have removed; it changes nothing.
            if (ApOpDiagnostics.enabled) currentNode.probeAnyTrim(ap)

            val (updatedAddedNode, addedInitial) = currentNode.mergeAddDelta(ap, foldToAny = false)

            if (addedInitial == null) return null

            stats?.recordArrival(currentNode, ap, updatedAddedNode)

            this.added = internIfRequired(interner, updatedAddedNode)

            intern(interner)

            return addedInitial
        }

        private var operationsBeforeIntern = INTERN_RATE

        private fun internIfRequired(interner: AccessTreeSoftInterner, node: AccessTreeNode): AccessTreeNode {
            if (node.size < SIZE_TO_FORCE_INTERN) return node
            return interner.intern(node)
        }

        private fun intern(interner: AccessTreeSoftInterner) {
            val current = added ?: return

            if (operationsBeforeIntern-- > 0) return
            if (current.size < INTERN_SIZE_REQUIREMENT) return

            operationsBeforeIntern = INTERN_RATE
            added = interner.intern(current)
        }

        fun addAnalyzedInitialFact(ap: AccessPath.AccessNode?, exclusions: IntOpenHashSet): Boolean =
            AccessPathTrieNode.add(analyzed, ap, exclusions)
    }

    class AccessPathTrieNode {
        private var children: Int2ObjectOpenHashMap<AccessPathTrieNode>? = null
        private var terminals: IntOpenHashSet? = null

        fun exclusions(): IntOpenHashSet? = terminals

        fun child(accessor: AccessorIdx): AccessPathTrieNode? =
            children?.get(accessor)

        fun forEachChild(body: (AccessorIdx, AccessPathTrieNode) -> Unit) {
            val children = this.children ?: return
            val iterator = children.int2ObjectEntrySet().fastIterator()
            while (iterator.hasNext()) {
                val entry = iterator.next()
                body(entry.intKey, entry.value)
            }
        }

        private fun getTerminals(): IntOpenHashSet =
            terminals ?: IntOpenHashSet().also { terminals = it }

        private fun getChildren(): Int2ObjectOpenHashMap<AccessPathTrieNode> =
            children ?: Int2ObjectOpenHashMap<AccessPathTrieNode>().also { children = it }

        companion object {
            fun empty() = AccessPathTrieNode()

            fun add(
                initialRoot: AccessPathTrieNode,
                initialAccess: AccessPath.AccessNode?,
                exclusions: IntOpenHashSet,
            ): Boolean {
                var trieNode = initialRoot
                var access = initialAccess

                while (true) {
                    if (access == null) {
                        var modified = trieNode.terminals == null
                        modified = modified or trieNode.getTerminals().addAll(exclusions)
                        return modified
                    }

                    val key = access.accessor
                    trieNode = trieNode.getChildren().getOrPut(key) { empty() }
                    access = access.next
                }
            }
        }
    }

    companion object {
        private const val INTERN_RATE = 100
        private const val INTERN_SIZE_REQUIREMENT = 1_000
        private const val SIZE_TO_FORCE_INTERN = 100_000

        /**
         * `-Dopentaint.tifaNoUncoveredFrontier=true`, default **false**. The positive control on the
         * control, design §9.2: with R3b off, conductor must lose `ssrf` and `path-traversal` and
         * report `Total vulnerabilities: 0`. A suite that cannot detect the known failure is not
         * validating anything.
         */
        /**
         * `-Dopentaint.tifaNoAnyFrontier=true`. Suppresses R3a, the coarse `p.[any]` edge, leaving
         * R3c to answer covered demand and R3b to answer uncovered demand.
         */
        /**
         * ABLATION CONTROLS. Each turns off exactly one rule, and each is UNSOUND on its own -- they
         * exist to make a claim about a rule falsifiable, not to be run in anger.
         *
         * They earned their keep on the first gate: the one new failure this change produced,
         * `TreeCleanerFieldSensitivityAnalysisTest.concrete two-level clean over an abstract
         * source`, survived R3a-off, R3c-off, R4-off and single-round, and died only when the
         * `[any]`-carrying premise disappeared entirely. That is what identified the mechanism
         * rather than a plausible story about it.
         *
         *  - `-Dopentaint.tifaNoSynthesised` -- R3c off. Demand for an accessor no concrete branch
         *    holds goes unanswered; the eight cross-backend `any accessor scenario` cases go red.
         *  - `-Dopentaint.tifaNoVirtualDescent` -- R4 off. The abstraction sticks one level below
         *    every `[any]`: premises are handed out and never descended past.
         *  - `-Dopentaint.tifaSingleRound` -- one walk per call. Correct but lazy; a depth-`k`
         *    premise then needs `k` triggering events instead of one.
         */
        @JvmField
        val SUPPRESS_SYNTHESISED: Boolean =
            System.getProperty("opentaint.tifaNoSynthesised")?.trim().toBoolean()

        @JvmField
        val SUPPRESS_VIRTUAL_DESCENT: Boolean =
            System.getProperty("opentaint.tifaNoVirtualDescent")?.trim().toBoolean()

        @JvmField
        val SINGLE_ROUND: Boolean =
            System.getProperty("opentaint.tifaSingleRound")?.trim().toBoolean()

        /**
         * R3a, the coarse `p.[any]` premise: `-Dopentaint.tifaAnyFrontierPremise=true`, default
         * **OFF**. This overturns design §7 R5, which resolved the question in favour of ALWAYS, and
         * the reason is a measurement the design did not have.
         *
         * An `[any]` premise's entry fact `R.[any].*` cannot express a node deletion INSIDE the
         * `[any]`, so a cleaner that bites on a concrete path stops biting under it. With this on,
         * `TreeCleanerFieldSensitivityAnalysisTest.concrete two-level clean over an abstract source`
         * resurrects the sanitized field -- one false positive, in the gate, reproducible; with it
         * off the suite is green and nothing else moves.
         *
         * The old code had exactly this guard, spelled `!enumerateAnyFrontier`: emit the coarse edge
         * only once the base has stopped enumerating, because while concrete premises are still
         * being handed out the coarse one alongside them can only add false positives. R1 does not
         * remove that argument -- it makes it unconditional. There is no cap any more, so the
         * enumeration never stops, so the old guard is never satisfied. R3c answers every covered
         * demand precisely and R3b answers the uncovered frontier; the coarse edge is left with
         * nothing to answer that they do not.
         *
         * Kept, not deleted, because the premise SHAPE is still load-bearing elsewhere -- summaries
         * keyed on an `[any]` premise, `splitDelta` stepping over one, `AccessBasedStorage`'s
         * `[any]`-keyed lookup -- and because it is the arm to reach for if a workload ever shows
         * that the enumeration, rather than the materialisation, is what has to be bounded.
         */
        @JvmField
        val ANY_FRONTIER_PREMISE: Boolean =
            System.getProperty("opentaint.tifaAnyFrontierPremise")?.trim().toBoolean()

        @JvmField
        val SUPPRESS_UNCOVERED_FRONTIER: Boolean =
            System.getProperty("opentaint.tifaNoUncoveredFrontier")?.trim().toBoolean()
    }
}

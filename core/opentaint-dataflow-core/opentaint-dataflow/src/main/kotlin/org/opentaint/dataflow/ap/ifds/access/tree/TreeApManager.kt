package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet.Empty
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.AnyMatchMode
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactSideEffectSummariesApStorage
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactList
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodAccessPathSubscription
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesNDInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodNDInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import org.opentaint.ir.api.common.cfg.CommonInst

class TreeApManager(
    override val anyAccessorUnrollStrategy: AnyAccessorUnrollStrategy,
    refManager: RefManager,
    override val cancellation: Cancellation,
    /**
     * `L`, the per-`[any]`-origin unroll budget. A constructor parameter rather than a direct read of
     * the property so a test can pin a limit without touching global state, exactly as
     * [TreeInitialFactAbstraction] does.
     */
    anyUnrollLimit: Int = AnyUnrollManager.DEFAULT_ANY_UNROLL_LIMIT,
    /** What kind the survivor of a union carries; a constructor parameter for the same reason. */
    anyUnrollKindMerge: AnyUnrollKindMerge = AnyUnrollManager.DEFAULT_KIND_MERGE,
    /**
     * Whether the MATCHING channels read `[any]` LITERALLY.
     *
     * `[any]` is read two different ways depending on the question being asked, and before this flag
     * it was read the same way for both:
     *
     *  - **denotation** -- `readAccessor`, `startsWithAccessor`, `contains`/`equalTo`; the cleaner,
     *    the rule preconditions, alias analysis, trace resolution. `[any]` is zero-or-more covered
     *    steps. This flag does not touch them.
     *  - **matching** -- which premise a fact activates: [AccessTree.delta],
     *    [AccessTree.AccessNode.filterStartsWith], the [AccessBasedStorage] premise lookup, and the
     *    initial-fact abstraction's descent. Here a premise link matches only a LITERAL child, or a
     *    child sitting directly under the node's `[any]` edge (`[any]` taken zero times).
     *
     * The term this drops -- synthesising a concrete accessor OUT of an `[any]` -- is the unique
     * step that consumes a premise link without descending the fact, which is what makes the
     * summary-application round trip a ratchet (`AnyDeltaConcatRoundTripTest`) and what lets
     * `TreeInitialFactAbstraction`'s R3c/R4 ladder walk `sum n!/(n-k)!` premises. With it gone a
     * fact's premises are exactly its literal prefixes.
     *
     * Design: `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md`. A constructor
     * parameter rather than a direct property read so a test can pin it without global state.
     */
    @JvmField
    val literalAnyMatch: Boolean = DEFAULT_LITERAL_ANY_MATCH,
) : ApManager {
    /**
     * A part rung, resolved against the manager-wide setting.
     *
     * Note what the test is: the CONSTRUCTOR ARGUMENT against the global option, computed once, and
     * NOT each intermediate rung against it. Testing the rung would break the chain -- setting
     * `-Dopentaint.literalAnyMatch.premises=false` would move `literalAnyPremises` off the global
     * default and thereby make the finer `.premises.r3c` / `.premises.r4` rungs beneath it
     * unreachable, which is the opposite of what a bisect ladder is for.
     */
    private val instanceOverridesMode: Boolean = literalAnyMatch != DEFAULT_LITERAL_ANY_MATCH

    private fun part(name: String, wide: Boolean): Boolean =
        if (instanceOverridesMode) wide else AnyMatchMode.part(name) ?: wide

    /**
     * The rule, split into the three places it applies, so an ablation can attribute a lost finding
     * to one of them instead of to "the change".
     *
     * Each defaults to [literalAnyMatch] and can be refined on its own with
     * `-Dopentaint.literalAnyMatch.reader|lookup|premises=true|false`. They are NOT independent
     * settings a caller should ship: `premises` without `reader` emits premises nothing can match,
     * and `reader` without `premises` leaves TIFA handing out concrete premises for no reason. They
     * exist to bisect.
     *
     * **An explicit per-instance [literalAnyMatch] beats every part property.** The rung only
     * refines the GLOBAL default; see [part]. Before this, a `.part` property set on the JVM
     * overrode a manager deliberately constructed in the other mode, so `literalAnyMatch = false` in
     * a test meant "false unless some `-D` the test never set says otherwise".
     */
    @JvmField
    val literalAnyReader: Boolean = part("reader", literalAnyMatch)

    @JvmField
    val literalAnyLookup: Boolean = part("lookup", literalAnyMatch)

    @JvmField
    val literalAnyPremises: Boolean = part("premises", literalAnyMatch)

    /** Ablation only, one rung finer than [literalAnyPremises]: R3c, R4 and R3b's second edge. */
    @JvmField
    val dropR3c: Boolean = part("premises.r3c", literalAnyPremises)

    @JvmField
    val dropR4: Boolean = part("premises.r4", literalAnyPremises)

    val refManager = refManager.softRefManager("Tree")

    /**
     * Whether `[any]` semantics may be QUERIED at all on this manager.
     *
     * [AnyAccessorUnrollStrategy.AnyAccessorDisabled] -- installed for the whole prescan phase --
     * does not return `false` from [AnyAccessorUnrollStrategy.unrollAccessor], it **throws**. That is
     * deliberate: the prescan's contract is that no `[any]` reaches it, and a swallowing wrapper
     * would turn a loud violation into a silent mis-analysis. But it means every path that might
     * reach [isCoveredByAny] has to prove an `[any]` edge exists first, or short-circuit before it --
     * and the nested-`[any]` normalisation runs from the node factory, which cannot make either
     * argument. So it short-circuits on this instead.
     */
    @JvmField
    val anyAccessorsQueryable: Boolean =
        anyAccessorUnrollStrategy !== AnyAccessorUnrollStrategy.AnyAccessorDisabled

    /**
     * Allocation, union and charging for the `[any]` unroll automata.
     *
     * It lives here because this is the single object every tree-backend site already holds, and the
     * only common ancestor of the two spend sites -- the initial-fact abstraction under the callee's
     * analyzer, and the access-path subscription under the caller's. Putting it here is what makes
     * the budget genuinely SHARED rather than partitioned per `(entry point, base)`, which is the
     * failure that made the previous cap ineffective.
     */
    @JvmField
    val anyUnroll = AnyUnrollManager(if (anyAccessorsQueryable) anyUnrollLimit else -1, anyUnrollKindMerge)

    val interner = AccessorInterner()

    val Accessor.idx: AccessorIdx
        get() = interner.index(this)

    val AccessorIdx.accessor: Accessor
        get() = interner.accessor(this)
            ?: error("Accessor not found: $this")

    fun isCoveredByAny(accessor: AccessorIdx) =
        anyAccessorUnrollStrategy.unrollAccessor(accessor.accessor)

    override fun initialFactAbstraction(methodInitialStatement: CommonInst): InitialFactAbstraction =
        TreeInitialFactAbstraction(this, methodInitialStatement)

    override fun methodEdgesFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesFinalApSet =
        MethodEdgesFinalTreeApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesInitialToFinalApSet = MethodEdgesInitialToFinalTreeApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesNDInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesNDInitialToFinalApSet =
        MethodEdgesNDInitialToFinalTreeApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun accessPathSubscription(): MethodAccessPathSubscription =
        MethodTreeAccessPathSubscription(this)

    override fun sideEffectRequirementApStorage(): SideEffectRequirementApStorage =
        SideEffectRequirementTreeApStorage(this)

    override fun methodFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodFinalApSummariesStorage =
        MethodFinalTreeApSummariesStorage(methodInitialStatement, this)

    override fun methodInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodInitialToFinalApSummariesStorage =
        MethodInitialToFinalApSummaries(methodInitialStatement, this)

    override fun methodNDInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodNDInitialToFinalApSummariesStorage =
        MethodNDInitialToFinalApSummaries(methodInitialStatement, this)

    override fun factSideEffectSummariesApStorage(methodInitialStatement: CommonInst): FactSideEffectSummariesApStorage =
        FactSideEffectSummariesTreeApStorage(methodInitialStatement, this)

    override fun listEdgeCompressionRequired(edge: Edge): Boolean {
        val fact = when (edge) {
            is Edge.ZeroToZero -> return false
            is Edge.FactToFact -> edge.factAp
            is Edge.NDFactToFact -> edge.factAp
            is Edge.ZeroToFact -> edge.factAp
        }
        return TreeFinalFactList.factCompressionRequired(fact)
    }

    override fun reportApStats(): String? = anyUnroll.liveReport()

    override fun finalFactList(): FinalFactList = TreeFinalFactList(this)

    override fun mostAbstractInitialAp(base: AccessPathBase): InitialFactAp =
        AccessPath(this, base, access = null, exclusions = Empty)

    override fun mostAbstractFinalAp(base: AccessPathBase): FinalFactAp =
        AccessTree(this, base, abstractNode, exclusions = Empty)

    override fun createFinalAp(base: AccessPathBase, exclusions: ExclusionSet): FinalFactAp =
        AccessTree(this,base, finalNode, exclusions)

    override fun createFinalInitialAp(base: AccessPathBase, exclusions: ExclusionSet): InitialFactAp =
        AccessPath(this, base, access = null, exclusions).prependAccessor(FinalAccessor)

    override fun createSerializer(context: SummarySerializationContext): ApSerializer {
        return TreeSerializer(this, context)
    }

    val emptyNode = AccessNode.createInitialNode(
        this,
        isAbstract = false, isFinal = false,
    )

    val abstractNode = AccessNode.createInitialNode(
        this,
        isAbstract = true, isFinal = false,
    )

    val finalNode = AccessNode.createInitialNode(
        this,
        isAbstract = false, isFinal = true,
    )

    val abstractFinalNode = AccessNode.createInitialNode(
        this,
        isAbstract = true, isFinal = true,
    )

    companion object {
        const val LITERAL_ANY_MATCH_PROPERTY = AnyMatchMode.LITERAL_ANY_MATCH_PROPERTY

        /**
         * `-Dopentaint.absorbSiblings=true`, default off. Fold every COVERED sibling of a node's own
         * `[any]` into that `[any]`'s subtree, on the result of every edge-store merge. See
         * `AccessTree.AccessNode.compressAbsorbCoveredSiblings`.
         */
        @JvmStatic
        val ABSORB_SIBLINGS: Boolean = boolProperty("opentaint.absorbSiblings") ?: false

        /**
         * The global option, and the only thing that decides the mode for a manager built without an
         * explicit argument. Delegates to [AnyMatchMode.literal] -- one parse, one place to look.
         */
        @JvmStatic
        val DEFAULT_LITERAL_ANY_MATCH: Boolean get() = AnyMatchMode.literal

        private fun boolProperty(name: String): Boolean? = AnyMatchMode.boolProperty(name)
    }
}

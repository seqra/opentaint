package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.FactNDEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.SummaryEdgeSubscriptionManager.ZeroEdgeSummarySubscription
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodAccessPathSubscription
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.MethodTreeAccessPathSubscription
import org.opentaint.ir.api.common.cfg.CommonInst

/**
 * Suffix-native F2F caller-subscription relation. Zero and non-distributive subscriptions keep the
 * established Tree implementation; only the paired relation is replaced here.
 */
class MethodSuffixTreeAccessPathSubscription(
    private val apManager: SuffixTreeApManager,
) : MethodAccessPathSubscription {
    private data class CellKey(
        val callerEp: CommonInst,
        val calleeInitialBase: AccessPathBase,
        val callerInitialBase: AccessPathBase,
        val callerFinalBase: AccessPathBase,
    )

    private data class SeenPremise(
        val key: CellKey,
        val accessors: List<Int>,
        val exclusions: Set<Int>,
    )

    private val treeDelegate = MethodTreeAccessPathSubscription(apManager)
    private val cells = HashMap<CellKey, SuffixRelationTrie>()
    // Cone annihilation is correct for the propagated relation, but a later callee summary lookup
    // still needs the concrete caller witness that introduced a covered cone. Keep those exact
    // generators as a lookup index; results are materialized only at this summary-application seam.
    private val lookupGenerators = HashMap<CellKey, LinkedHashSet<SuffixGenerator>>()
    private val seenPremises = HashSet<SeenPremise>()

    override fun addZeroToFact(
        callerEp: CommonInst,
        calleeInitialFactBase: AccessPathBase,
        callerFactAp: FinalFactAp,
    ): ZeroEdgeSummarySubscription? =
        treeDelegate.addZeroToFact(callerEp, calleeInitialFactBase, callerFactAp)

    override fun addNDFactToFact(
        callerEp: CommonInst,
        calleeInitialBase: AccessPathBase,
        callerInitial: Set<InitialFactAp>,
        callerExitAp: FinalFactAp,
    ): FactNDEdgeSummarySubscription? =
        treeDelegate.addNDFactToFact(callerEp, calleeInitialBase, callerInitial, callerExitAp)

    override fun addFactToFact(
        callerEp: CommonInst,
        calleeInitialBase: AccessPathBase,
        callerInitialAp: InitialFactAp,
        callerExitAp: FinalFactAp,
    ): FactEdgeSummarySubscription? =
        addFactToFactEdges(
            callerEp,
            calleeInitialBase,
            callerInitialAp,
            callerExitAp,
            suffixBundle = null,
        ).firstOrNull()

    override fun addFactToFactEdges(
        callerEp: CommonInst,
        calleeInitialBase: AccessPathBase,
        callerInitialAp: InitialFactAp,
        callerExitAp: FinalFactAp,
        suffixBundle: SuffixEdgeBundle?,
    ): List<FactEdgeSummarySubscription> {
        check(callerInitialAp.exclusions == callerExitAp.exclusions) {
            "Subscription edge exclusion mismatch"
        }
        val key = CellKey(
            callerEp,
            calleeInitialBase,
            callerInitialAp.base,
            callerExitAp.base,
        )
        val relation = cells.getOrPut(key, ::SuffixRelationTrie)
        val lookup = lookupGenerators.getOrPut(key, ::LinkedHashSet)
        val changedGenerators = ArrayList<SuffixGenerator>()
        val premiseGenerators = ArrayList<SuffixGenerator>()
        var premiseNew = false

        if (suffixBundle != null) {
            for (cone in suffixBundle.suffixTree.cones()) {
                val coneIsNewPremise = seenPremises.add(
                    SeenPremise(
                        key,
                        suffixBundle.initialPrefix + cone.suffix,
                        cone.exclusions,
                    )
                )
                premiseNew = coneIsNewPremise || premiseNew
                for (terminal in suffixBundle.finalPrefixTree.terminals()) {
                    val generator = SuffixGenerator(
                        suffixBundle.initialPrefix,
                        terminal.prefix,
                        cone.suffix,
                        cone.exclusions,
                        terminal.markers,
                    )
                    lookup += generator
                    if (relation.add(generator)) changedGenerators += generator
                    if (coneIsNewPremise) premiseGenerators += generator
                }
            }
        } else {
            val initial = callerInitialAp as? AccessPath
                ?: error("SuffixTree subscription received non-tree initial fact")
            val final = callerExitAp as? AccessTree
                ?: error("SuffixTree subscription received non-tree final fact")
            val initialPath = initial.access.toAccessorList()
            val exclusions = final.exclusions.toAccessorIndices()
            premiseNew = seenPremises.add(SeenPremise(key, initialPath, exclusions))
            for (terminal in final.access.terminals()) {
                val generator = relation.factor(
                    initialPath.toIntArray(),
                    terminal.accessors.toIntArray(),
                    exclusions,
                    terminal.markers,
                )
                lookup += generator
                if (relation.add(generator)) changedGenerators += generator
                if (premiseNew) premiseGenerators += generator
            }
        }

        if (changedGenerators.isEmpty()) {
            if (!premiseNew) return emptyList()
            return suffixDeltaBundles(premiseGenerators).map { bundledSubscription(key, it) }
        }

        SuffixTreeDiagnostics.logStoredShape(
            relation,
            identity = {
                key.callerInitialBase == key.callerFinalBase && it.isIdentityForSameBase()
            },
            site = { "subscription ${key.callerEp}" },
        )

        val deltaBundles = suffixDeltaBundles(changedGenerators)
        val publishedBundles = if (
            key.callerInitialBase == key.callerFinalBase &&
            changedGenerators.any { it.initialPrefix == it.finalPrefix }
        ) {
            deltaBundles.filterNot { it.isIdentityForSameBase() } +
                relation.bundles().filter { it.isIdentityForSameBase() }
        } else {
            deltaBundles
        }

        return publishedBundles
            .map { bundle ->
                SuffixTreeDiagnostics.recordPublished(
                    bundle,
                    identity = key.callerInitialBase == key.callerFinalBase &&
                        bundle.isIdentityForSameBase(),
                )
                bundledSubscription(key, bundle)
            }
    }

    override fun collectFactEdge(
        collection: MutableList<FactEdgeSummarySubscription>,
        summaryInitialFactAp: InitialFactAp,
        emptyDeltaRequired: Boolean,
    ) {
        val pattern = summaryInitialFactAp as? AccessPath
            ?: error("SuffixTree subscription received non-tree summary pattern")
        for ((key, generators) in lookupGenerators) {
            if (key.calleeInitialBase != pattern.base) continue
            for (generator in generators) {
                val exclusions = apManager.exclusions(generator.exclusions)
                val initial = AccessPath(
                    apManager,
                    key.callerInitialBase,
                    apManager.buildInitialPath(generator.initialPrefix + generator.suffix),
                    exclusions,
                )
                val finalNode = apManager.buildFinalPath(
                    generator.finalPrefix + generator.suffix,
                    generator.finalMarkers,
                ) ?: continue
                val filteredFinal = finalNode.filterStartsWith(pattern.access) ?: continue
                collection += subscription(
                    key,
                    initial,
                    AccessTree(apManager, key.callerFinalBase, filteredFinal, exclusions),
                    suffixBundle = null,
                )
            }
        }
    }

    override fun collectFactNDEdge(
        collection: MutableList<FactNDEdgeSummarySubscription>,
        summaryInitialFactAp: InitialFactAp,
        emptyDeltaRequired: Boolean,
    ) = treeDelegate.collectFactNDEdge(collection, summaryInitialFactAp, emptyDeltaRequired)

    override fun collectZeroEdge(
        collection: MutableList<ZeroEdgeSummarySubscription>,
        summaryInitialFactAp: InitialFactAp,
    ) = treeDelegate.collectZeroEdge(collection, summaryInitialFactAp)

    internal fun allBundles(): List<SuffixEdgeBundle> = cells.values.flatMap { it.bundles() }

    private fun bundledSubscription(
        key: CellKey,
        bundle: SuffixEdgeBundle,
    ): FactEdgeSummarySubscription {
        val initial = AccessPath(
            apManager,
            key.callerInitialBase,
            apManager.buildInitialPath(bundle.initialPrefix),
            ExclusionSet.Empty,
        )
        val final = AccessTree(
            apManager,
            key.callerFinalBase,
            apManager.buildFinalPrefixTree(bundle.finalPrefixTree) ?: apManager.abstractNode,
            ExclusionSet.Empty,
        )
        return subscription(key, initial, final, bundle)
    }

    private fun subscription(
        key: CellKey,
        initial: InitialFactAp,
        final: FinalFactAp,
        suffixBundle: SuffixEdgeBundle?,
    ): FactEdgeSummarySubscription = FactEdgeSummarySubscription()
        .setCalleeBase(key.calleeInitialBase)
        .setCallerInitialAp(initial)
        .setCallerAp(final)
        .setSuffixBundle(suffixBundle)

    private fun AccessPath.AccessNode?.toAccessorList(): List<Int> {
        if (this == null) return emptyList()
        val values = toList()
        return List(values.size) { values.getInt(it) }
    }

    private data class Terminal(val accessors: List<Int>, val markers: FinalPrefixMarkers)

    private fun AccessTree.AccessNode.terminals(): List<Terminal> = buildList {
        val path = ArrayList<Int>()
        fun visit(node: AccessTree.AccessNode) {
            if (node.isFinal || node.isAbstract) {
                add(Terminal(path.toList(), FinalPrefixMarkers(node.isFinal, node.isAbstract)))
            }
            node.forEachAccessor { accessor, child ->
                path.add(accessor)
                visit(child)
                path.removeAt(path.lastIndex)
            }
        }
        visit(this@terminals)
    }

    private fun ExclusionSet.toAccessorIndices(): Set<Int> = when (this) {
        ExclusionSet.Empty -> emptySet()
        ExclusionSet.Universe -> error("F2F subscription cannot have Universe exclusion")
        is ExclusionSet.Concrete -> with(apManager) { set.mapTo(hashSetOf()) { it.idx } }
    }
}

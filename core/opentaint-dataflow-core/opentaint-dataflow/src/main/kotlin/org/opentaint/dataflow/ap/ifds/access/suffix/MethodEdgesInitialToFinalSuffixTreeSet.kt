package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.ir.api.common.cfg.CommonInst

/** First suffix-native store: intra-method distributive edges grouped into edge-level bundles. */
class MethodEdgesInitialToFinalSuffixTreeSet(
    private val methodInitialStatement: CommonInst,
    maxInstIdx: Int,
    private val languageManager: LanguageManager,
    private val apManager: SuffixTreeApManager,
) : MethodEdgesInitialToFinalApSet {
    private data class Bases(val initial: AccessPathBase, val final: AccessPathBase)
    private data class SeenPremise(
        val statementIndex: Int,
        val bases: Bases,
        val accessors: List<Int>,
        val exclusions: Set<Int>,
    )

    private val cells = HashMap<Bases, Array<SuffixRelationTrie?>>()
    private val seenPremises = HashSet<SeenPremise>()
    private val storageSize = MethodAnalyzerEdges.instructionStorageSize(maxInstIdx)

    override fun add(
        statement: CommonInst,
        initialAp: InitialFactAp,
        finalAp: FinalFactAp,
    ): Pair<InitialFactAp, FinalFactAp>? =
        addFactToFact(statement, initialAp, finalAp, suffixBundle = null)
            .firstOrNull()
            ?.let { it.initial to it.final }

    override fun addFactToFact(
        statement: CommonInst,
        initialAp: InitialFactAp,
        finalAp: FinalFactAp,
        suffixBundle: SuffixEdgeBundle?,
    ): List<MethodEdgesInitialToFinalApSet.Addition> {
        check(initialAp.exclusions == finalAp.exclusions) { "Edge exclusion mismatch" }
        val bases = Bases(initialAp.base, finalAp.base)
        val statementIndex = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
        val relation = relationFor(bases, statementIndex)
        val changedGenerators = ArrayList<SuffixGenerator>()
        val premiseGenerators = ArrayList<SuffixGenerator>()
        var newPremise = false

        if (suffixBundle != null) {
            for (cone in suffixBundle.suffixTree.cones()) {
                val coneIsNewPremise = seenPremises.add(
                    SeenPremise(
                        statementIndex,
                        bases,
                        suffixBundle.initialPrefix + cone.suffix,
                        cone.exclusions,
                    )
                )
                newPremise = coneIsNewPremise || newPremise
                for (terminal in suffixBundle.finalPrefixTree.terminals()) {
                    val generator = SuffixGenerator(
                        initialPrefix = suffixBundle.initialPrefix,
                        finalPrefix = terminal.prefix,
                        suffix = cone.suffix,
                        exclusions = cone.exclusions,
                        finalMarkers = terminal.markers,
                    )
                    if (relation.add(generator)) changedGenerators.add(generator)
                    if (coneIsNewPremise) premiseGenerators.add(generator)
                }
            }
        } else {
            val initial = initialAp as? AccessPath
                ?: error("SuffixTree store received a non-tree initial fact: ${initialAp::class}")
            val final = finalAp as? AccessTree
                ?: error("SuffixTree store received a non-tree final fact: ${finalAp::class}")
            val initialPath = initial.access.toAccessorList()
            val exclusions = finalAp.exclusions.toAccessorIndices()
            newPremise = seenPremises.add(
                SeenPremise(statementIndex, bases, initialPath, exclusions)
            )

            for (terminal in final.access.terminals()) {
                val generator = relation.factor(
                    initialPath.toIntArray(),
                    terminal.accessors.toIntArray(),
                    exclusions,
                    terminal.markers,
                )
                if (relation.add(generator)) changedGenerators.add(generator)
                if (newPremise) premiseGenerators.add(generator)
            }
        }

        if (changedGenerators.isEmpty()) {
            if (!newPremise) return emptyList()
            return suffixDeltaBundles(premiseGenerators).map { bundleAddition(bases, it) }
        }

        SuffixTreeDiagnostics.logStoredShape(
            relation,
            identity = { bases.initial == bases.final && it.isIdentityForSameBase() },
            site = { "method $methodInitialStatement at $statement" },
        )

        val deltaBundles = suffixDeltaBundles(changedGenerators)
        val publishedBundles = if (
            bases.initial == bases.final && changedGenerators.any { it.initialPrefix == it.finalPrefix }
        ) {
            deltaBundles.filterNot { it.isIdentityForSameBase() } +
                relation.bundles().filter { it.isIdentityForSameBase() }
        } else {
            deltaBundles
        }

        return publishedBundles
            .asSequence()
            .map { bundle ->
                SuffixTreeDiagnostics.recordPublished(
                    bundle = bundle,
                    identity = bases.initial == bases.final && bundle.isIdentityForSameBase(),
                )
                bundleAddition(bases, bundle)
            }
            .toList()
    }

    override fun collectApAtStatement(
        collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        statement: CommonInst,
    ) {
        forEachMaterialized(statement) { _, pair -> collection.add(pair) }
    }

    override fun collectApAtStatement(
        collection: MutableList<Pair<InitialFactAp, FinalFactAp>>,
        statement: CommonInst,
        finalFactPattern: InitialFactAp,
    ) {
        forEachMaterialized(statement) { bases, pair ->
            if (bases.final == finalFactPattern.base) collection.add(pair)
        }
    }

    override fun collectApAtStatement(
        collection: MutableList<FinalFactAp>,
        statement: CommonInst,
        initialAp: InitialFactAp,
        finalFactPattern: InitialFactAp,
    ) {
        val exact = ArrayList<FinalFactAp>()
        val covered = ArrayList<FinalFactAp>()
        forEachMaterialized(statement) { bases, pair ->
            if (bases.initial != initialAp.base || bases.final != finalFactPattern.base) return@forEachMaterialized
            if (pair.first == initialAp) {
                exact.add(pair.second)
            } else if (pair.first.toFinalFact().contains(initialAp)) {
                covered.add(pair.second)
            }
        }
        collection.addAll(if (exact.isNotEmpty()) exact else covered)
    }

    internal fun bundlesAt(statement: CommonInst): List<SuffixEdgeBundle> {
        val statementIndex = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
        return buildList {
            for (relations in cells.values) relations.getOrNull(statementIndex)?.bundles()?.let(::addAll)
        }
    }

    private fun bundleAddition(
        bases: Bases,
        bundle: SuffixEdgeBundle,
    ): MethodEdgesInitialToFinalApSet.Addition {
        val initial = AccessPath(
            apManager,
            bases.initial,
            apManager.buildInitialPath(bundle.initialPrefix),
            ExclusionSet.Empty,
        )
        val final = AccessTree(
            apManager,
            bases.final,
            apManager.buildFinalPrefixTree(bundle.finalPrefixTree) ?: apManager.abstractNode,
            ExclusionSet.Empty,
        )
        return MethodEdgesInitialToFinalApSet.Addition(initial, final, bundle)
    }

    private inline fun forEachMaterialized(
        statement: CommonInst,
        action: (Bases, Pair<InitialFactAp, FinalFactAp>) -> Unit,
    ) {
        val statementIndex = MethodAnalyzerEdges.instructionStorageIdx(statement, languageManager)
        for ((bases, relations) in cells) {
            val relation = relations.getOrNull(statementIndex) ?: continue
            for (bundle in relation.bundles()) {
                for (cone in bundle.suffixTree.cones()) {
                    val exclusions = apManager.exclusions(cone.exclusions)
                    val initial = AccessPath(
                        apManager,
                        bases.initial,
                        apManager.buildInitialPath(bundle.initialPrefix + cone.suffix),
                        exclusions,
                    )
                    for (terminal in bundle.finalPrefixTree.terminals()) {
                        val finalNode = apManager.buildFinalPath(
                            terminal.prefix + cone.suffix,
                            terminal.markers,
                        ) ?: continue
                        val final = AccessTree(apManager, bases.final, finalNode, exclusions)
                        action(bases, initial to final)
                    }
                }
            }
        }
    }

    private fun relationFor(bases: Bases, statementIndex: Int): SuffixRelationTrie {
        val relations = cells.getOrPut(bases) { arrayOfNulls(storageSize) }
        return relations[statementIndex] ?: SuffixRelationTrie().also { relations[statementIndex] = it }
    }

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
        ExclusionSet.Universe -> error("F2F edge cannot have Universe exclusion")
        is ExclusionSet.Concrete -> with(apManager) { set.mapTo(hashSetOf()) { it.idx } }
    }
}

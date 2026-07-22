package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Edge
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactToFactEdgeBuilder
import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.MethodInitialToFinalApSummaries
import org.opentaint.ir.api.common.cfg.CommonInst

/** Persistent F2F summary relation storing and publishing grouped suffix bundles. */
class MethodInitialToFinalSuffixTreeSummaries(
    private val methodInitialStatement: CommonInst,
    private val apManager: SuffixTreeApManager,
) : MethodInitialToFinalApSummariesStorage {
    private data class CellKey(
        val exitStatement: CommonInst,
        val initialBase: AccessPathBase,
        val finalBase: AccessPathBase,
    )
    private val cells = HashMap<CellKey, SuffixRelationTrie>()
    private val finalSideCanonicalizers = HashMap<CellKey, FinalSideSummaryCanonicalizer>()
    private val seenPremises = HashSet<Pair<CellKey, List<Int>>>()
    private val treeShadow = if (SuffixTreeDiagnostics.verifySummaries) {
        MethodInitialToFinalApSummaries(methodInitialStatement, apManager)
    } else {
        null
    }

    @Synchronized
    override fun add(edges: List<Edge.FactToFact>, added: MutableList<FactToFactEdgeBuilder>) {
        val materialized = edges.flatMap { it.materializeSuffixes() }
        treeShadow?.add(materialized, mutableListOf())
        for (edge in edges) add(edge, added)
        for (edge in materialized) addFinalSideCanonicalization(edge, added)
        treeShadow?.let(::verifyAgainstTreeShadow)
    }

    private fun addFinalSideCanonicalization(
        edge: Edge.FactToFact,
        added: MutableList<FactToFactEdgeBuilder>,
    ) {
        val initial = edge.initialFactAp as AccessPath
        val final = edge.factAp as AccessTree
        val key = CellKey(edge.statement, initial.base, final.base)
        val relation = cells.getOrPut(key, ::SuffixRelationTrie)
        val canonicalizer = finalSideCanonicalizers.getOrPut(key) {
            FinalSideSummaryCanonicalizer(relation, apManager)
        }
        val changed = canonicalizer.add(
            initial.access,
            final.access,
            final.exclusions.toAccessorIndices(),
        )
        publishChanged(key, relation, changed, added)
    }

    private fun add(edge: Edge.FactToFact, added: MutableList<FactToFactEdgeBuilder>) {
        val key = CellKey(edge.statement, edge.initialFactAp.base, edge.factAp.base)
        val relation = cells.getOrPut(key, ::SuffixRelationTrie)
        val changedGenerators = ArrayList<SuffixGenerator>()
        var premiseNew = false

        val bundle = edge.suffixBundle
        if (bundle != null) {
            for (cone in bundle.suffixTree.cones()) {
                for (terminal in bundle.finalPrefixTree.terminals()) {
                    val generator = SuffixGenerator(
                        bundle.initialPrefix,
                        terminal.prefix,
                        cone.suffix,
                        cone.exclusions,
                        terminal.markers,
                    )
                    if (relation.add(generator)) changedGenerators.add(generator)
                    val materializedInitial = apManager
                        .buildInitialPath(generator.initialPrefix + generator.suffix)
                        .toAccessorList()
                    premiseNew = seenPremises.add(key to materializedInitial) || premiseNew
                }
            }
        } else {
            val initial = edge.initialFactAp as? AccessPath
                ?: error("SuffixTree summary received a non-tree initial fact: ${edge.initialFactAp::class}")
            val final = edge.factAp as? AccessTree
                ?: error("SuffixTree summary received a non-tree final fact: ${edge.factAp::class}")
            val initialPath = initial.access.toAccessorList()
            premiseNew = seenPremises.add(key to initialPath)
            val exclusions = edge.factAp.exclusions.toAccessorIndices()
            for (terminal in final.access.terminals()) {
                val generator = relation.factor(
                    initialPath.toIntArray(),
                    terminal.accessors.toIntArray(),
                    exclusions,
                    terminal.markers,
                )
                if (relation.add(generator)) changedGenerators.add(generator)
            }
        }

        if (changedGenerators.isEmpty()) {
            if (premiseNew) {
                added += FactToFactEdgeBuilder()
                    .setInitialAp(edge.initialFactAp)
                    .setExitAp(edge.factAp)
                    .setExitStatement(edge.statement)
                    .setSuffixBundle(edge.suffixBundle)
            }
            return
        }

        publishChanged(key, relation, changedGenerators, added)
    }

    private fun publishChanged(
        key: CellKey,
        relation: SuffixRelationTrie,
        changedGenerators: List<SuffixGenerator>,
        added: MutableList<FactToFactEdgeBuilder>,
    ) {
        if (changedGenerators.isEmpty()) return
        SuffixTreeDiagnostics.logStoredShape(
            relation,
            identity = {
                key.initialBase == key.finalBase && it.isIdentityForSameBase()
            },
            site = { "summary ${key.exitStatement}" },
        )

        suffixDeltaBundles(changedGenerators)
            .mapTo(added) {
                SuffixTreeDiagnostics.recordPublished(
                    bundle = it,
                    identity = key.initialBase == key.finalBase && it.isIdentityForSameBase(),
                )
                bundleBuilder(key, it)
            }
    }

    @Synchronized
    override fun filterEdgesTo(
        dst: MutableList<FactToFactEdgeBuilder>,
        initialFactPattern: FinalFactAp?,
        finalFactBase: AccessPathBase?,
    ) {
        for ((key, relation) in cells) {
            if (initialFactPattern != null && key.initialBase != initialFactPattern.base) continue
            if (finalFactBase != null && key.finalBase != finalFactBase) continue

            for (bundle in relation.bundles()) {
                val filtered = if (initialFactPattern == null) {
                    bundle
                } else {
                    filterBundle(bundle, initialFactPattern) ?: continue
                }
                dst += bundleBuilder(key, filtered)
            }
        }
    }

    internal fun allBundles(): List<SuffixEdgeBundle> = cells.values.flatMap { it.bundles() }

    private fun verifyAgainstTreeShadow(shadow: MethodInitialToFinalApSummaries) {
        val builders = mutableListOf<FactToFactEdgeBuilder>()
        shadow.filterEdgesTo(builders, initialFactPattern = null, finalFactBase = null)
        val entryPoint = MethodEntryPoint(EmptyMethodContext, methodInitialStatement)
        val shadowRelations = HashMap<CellKey, SuffixRelationTrie>()

        for (builder in builders) {
            val edge = builder.setEntryPoint(entryPoint).build()
            val key = CellKey(edge.statement, edge.initialFactAp.base, edge.factAp.base)
            val relation = shadowRelations.getOrPut(key, ::SuffixRelationTrie)
            edge.generators().forEach { relation.add(it) }
        }

        for ((key, shadowRelation) in shadowRelations) {
            val suffixRelation = cells[key]
                ?: error("SuffixTree lost Tree summary cell $key")
            for (generator in shadowRelation.generators()) {
                check(suffixRelation.isCovered(generator)) {
                    "SuffixTree summary does not subsume Tree summary at $key: $generator"
                }
            }
        }

        if (cells.values.none { it.hasSquashed }) {
            for ((key, suffixRelation) in cells) {
                val shadowRelation = shadowRelations[key]
                    ?: error("SuffixTree has an extra unsquashed summary cell $key")
                for (generator in suffixRelation.generators()) {
                    check(shadowRelation.isCovered(generator)) {
                        "Unsquashed SuffixTree summary differs from Tree summary at $key: $generator"
                    }
                }
            }
        }
    }

    private fun Edge.FactToFact.generators(): List<SuffixGenerator> {
        val bundle = suffixBundle
        if (bundle != null) {
            return buildList {
                for (cone in bundle.suffixTree.cones()) {
                    for (terminal in bundle.finalPrefixTree.terminals()) {
                        add(
                            SuffixGenerator(
                                bundle.initialPrefix,
                                terminal.prefix,
                                cone.suffix,
                                cone.exclusions,
                                terminal.markers,
                            )
                        )
                    }
                }
            }
        }

        val initial = initialFactAp as AccessPath
        val final = factAp as AccessTree
        val initialPath = initial.access.toAccessorList()
        val exclusions = final.exclusions.toAccessorIndices()
        return final.access.terminals().map { terminal ->
            SuffixRelationTrie().factor(
                initialPath.toIntArray(),
                terminal.accessors.toIntArray(),
                exclusions,
                terminal.markers,
            )
        }
    }

    private fun filterBundle(bundle: SuffixEdgeBundle, pattern: FinalFactAp): SuffixEdgeBundle? {
        val matchingCones = bundle.suffixTree.cones().filter { cone ->
            val initial = AccessPath(
                apManager,
                pattern.base,
                apManager.buildInitialPath(bundle.initialPrefix + cone.suffix),
                apManager.exclusions(cone.exclusions),
            )
            pattern.contains(initial)
        }
        if (matchingCones.isEmpty()) return null
        if (matchingCones.size == bundle.suffixTree.cones().size) return bundle
        return bundle.copy(suffixTree = SuffixTree.fromCones(matchingCones))
    }

    private fun bundleBuilder(key: CellKey, bundle: SuffixEdgeBundle): FactToFactEdgeBuilder {
        val initial = AccessPath(
            apManager,
            key.initialBase,
            apManager.buildInitialPath(bundle.initialPrefix),
            ExclusionSet.Empty,
        )
        val final = AccessTree(
            apManager,
            key.finalBase,
            apManager.buildFinalPrefixTree(bundle.finalPrefixTree) ?: apManager.abstractNode,
            ExclusionSet.Empty,
        )
        return FactToFactEdgeBuilder()
            .setInitialAp(initial)
            .setExitAp(final)
            .setExitStatement(key.exitStatement)
            .setSuffixBundle(bundle)
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
        ExclusionSet.Universe -> error("F2F summary cannot have Universe exclusion")
        is ExclusionSet.Concrete -> with(apManager) { set.mapTo(hashSetOf()) { it.idx } }
    }
}

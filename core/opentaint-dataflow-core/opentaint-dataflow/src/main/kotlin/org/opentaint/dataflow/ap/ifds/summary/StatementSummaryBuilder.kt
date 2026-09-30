package org.opentaint.dataflow.ap.ifds.summary

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary.BaseTransfer
import org.opentaint.dataflow.ap.ifds.summary.StatementSummary.Edge
import org.opentaint.ir.api.common.CommonType

class StatementSummaryBuilder(
    private val apManager: ApManager,
    private val keepAliasPropagationEdges: Boolean,
) {
    private val bases = ArrayList<AccessPathBase>(2)
    private val edges = ArrayList<ArrayList<Edge>>(2)
    private val filterBases = ArrayList<AccessPathBase>(2)
    private val filterTypes = ArrayList<CommonType>(2)

    fun build(): StatementSummary {
        val transfers = Array(bases.size) { i ->
            val base = bases[i]
            val types = filterTypes.filterIndexed { j, _ -> filterBases[j] == base }.distinct()
            BaseTransfer(base, edges[i].toTypedArray(), types.toTypedArray())
        }
        return StatementSummary(transfers)
    }

    fun buildReversed(): StatementSummary {
        val reversedEdges = Array(bases.size) { ArrayList<Edge>(2) }

        for (baseEdges in edges) {
            for (edge in baseEdges) {
                val to = edge.to ?: continue
                val idx = bases.indexOf(to.base)
                check(idx >= 0) { "Edge target is not a touched base: $edge" }

                reversedEdges[idx] += Edge(to.replaceExclusions(edge.from.exclusions), edge.from.replaceExclusions(ExclusionSet.Empty))
            }
        }

        return StatementSummary(Array(bases.size) { i ->
            BaseTransfer(bases[i], reversedEdges[i].toTypedArray(), emptyArray())
        })
    }

    fun fact(base: AccessPathBase, accessors: List<Accessor> = emptyList()): InitialFactAp =
        accessors.foldRight(apManager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }

    fun touch(base: AccessPathBase) {
        baseEdges(base)
    }

    fun edge(from: InitialFactAp, to: InitialFactAp?) {
        val baseEdges = baseEdges(from.base)
        val edge = Edge(from, to)
        if (edge !in baseEdges) baseEdges += edge
    }

    fun filter(base: AccessPathBase, type: CommonType?) {
        if (type == null) return
        filterBases += base
        filterTypes += type
    }

    fun move(to: AccessPathBase, from: AccessPathBase?, toAccessors: List<Accessor> = emptyList()) {
        touch(to)
        if (from == null) return
        edge(fact(from), fact(from))
        if (from != to || toAccessors.isNotEmpty()) edge(fact(from), fact(to, toAccessors))
    }

    fun read(
        to: AccessPathBase,
        base: AccessPathBase,
        accessors: List<Accessor>,
        toAccessors: List<List<Accessor>> = listOf(emptyList()),
    ) {
        val source = fact(base, accessors)

        touch(to)
        if (base != to) {
            keepAllExcept(base, accessors)
            edge(source, source)
        } else {
            edge(fact(base).exclude(accessors.first()), null)
        }
        for (targetAccessors in toAccessors) {
            edge(source, fact(to, targetAccessors))
        }
    }

    fun write(
        base: AccessPathBase,
        accessors: List<Accessor>,
        weak: Boolean,
        values: List<AccessPathBase>,
        aliasPaths: List<Pair<AccessPathBase, List<Accessor>>>,
    ) {
        touch(base)
        if (weak) {
            edge(fact(base), fact(base))
        } else {
            keepAllExcept(base, accessors)
        }

        for (value in values) {
            if (value != base) edge(fact(value), fact(value))
            edge(fact(value), fact(base, accessors))
        }

        for ((aliasBase, aliasAccessors) in aliasPaths) {
            if (aliasBase == base) continue
            val aliasPath = aliasAccessors + accessors
            aliasPropagation(aliasBase, aliasPath)
            for (value in values) {
                edge(fact(value), fact(aliasBase, aliasPath))
            }
        }
    }

    private fun baseEdges(base: AccessPathBase): ArrayList<Edge> {
        val idx = bases.indexOf(base)
        if (idx >= 0) return edges[idx]
        bases += base
        return ArrayList<Edge>(2).also { edges += it }
    }

    private fun keepAllExcept(base: AccessPathBase, accessors: List<Accessor>) {
        for (i in accessors.indices) {
            val prefix = fact(base, accessors.subList(0, i))
            edge(prefix.exclude(accessors[i]), prefix)
        }
    }

    private fun aliasPropagation(base: AccessPathBase, accessors: List<Accessor>) {
        if (!keepAliasPropagationEdges) return
        keepAllExcept(base, accessors)
        val target = fact(base, accessors)
        edge(target, target)
    }
}

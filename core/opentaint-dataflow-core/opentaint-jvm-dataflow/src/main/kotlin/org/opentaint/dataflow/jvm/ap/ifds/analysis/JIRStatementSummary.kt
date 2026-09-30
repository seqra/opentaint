package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.accessPathBase
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRReturnInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import org.opentaint.ir.api.jvm.cfg.JIRValue

class JIRStatementSummary(val transfers: Array<BaseTransfer>) {
    data class Edge(val from: InitialFactAp, val to: InitialFactAp?)

    class BaseTransfer(
        val base: AccessPathBase,
        val edges: Array<Edge>,
        val typeFilters: Array<JIRType>,
    )

    fun find(base: AccessPathBase): BaseTransfer? {
        for (transfer in transfers) {
            if (transfer.base == base) return transfer
        }
        return null
    }

    companion object {
        val Empty = JIRStatementSummary(emptyArray())

        fun build(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): JIRStatementSummary =
            builder(apManager, inst, aliasAnalysis, keepAliasPropagationEdges = false)?.build() ?: Empty

        fun buildReversed(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): JIRStatementSummary =
            builder(apManager, inst, aliasAnalysis, keepAliasPropagationEdges = true)?.buildReversed() ?: Empty

        private fun builder(
            apManager: ApManager,
            inst: JIRInst,
            aliasAnalysis: JIRLocalAliasAnalysis?,
            keepAliasPropagationEdges: Boolean,
        ): Builder? {
            val builder = Builder(apManager, inst, aliasAnalysis, keepAliasPropagationEdges)
            when (inst) {
                is JIRAssignInst -> builder.assign(inst.lhv, inst.rhv)
                is JIRReturnInst -> builder.move(AccessPathBase.Return, inst.returnValue?.let { accessPathBase(it) })
                is JIRThrowInst -> builder.move(AccessPathBase.Exception, accessPathBase(inst.throwable))
                else -> return null
            }
            return builder
        }
    }

    private class Builder(
        private val apManager: ApManager,
        private val inst: JIRInst,
        private val aliasAnalysis: JIRLocalAliasAnalysis?,
        private val keepAliasPropagationEdges: Boolean,
    ) {
        private val bases = ArrayList<AccessPathBase>(2)
        private val edges = ArrayList<ArrayList<Edge>>(2)
        private val filterBases = ArrayList<AccessPathBase>(2)
        private val filterTypes = ArrayList<JIRType>(2)

        fun build(): JIRStatementSummary {
            val transfers = Array(bases.size) { i ->
                val base = bases[i]
                val types = filterTypes.filterIndexed { j, _ -> filterBases[j] == base }.distinct()
                BaseTransfer(base, edges[i].toTypedArray(), types.toTypedArray())
            }
            return JIRStatementSummary(transfers)
        }

        fun buildReversed(): JIRStatementSummary {
            val reversedEdges = Array(bases.size) { ArrayList<Edge>(2) }

            for (baseEdges in edges) {
                for (edge in baseEdges) {
                    val to = edge.to ?: continue
                    val idx = bases.indexOf(to.base)
                    check(idx >= 0) { "Edge target is not a touched base: $edge" }

                    val reversed = Edge(to.replaceExclusions(edge.from.exclusions), edge.from.replaceExclusions(ExclusionSet.Empty))
                    if (reversed !in reversedEdges[idx]) reversedEdges[idx] += reversed
                }
            }

            return JIRStatementSummary(Array(bases.size) { i ->
                BaseTransfer(bases[i], reversedEdges[i].toTypedArray(), emptyArray())
            })
        }

        private fun fact(base: AccessPathBase, accessors: List<Accessor> = emptyList()): InitialFactAp =
            accessors.foldRight(apManager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }

        private fun touch(base: AccessPathBase): ArrayList<Edge> {
            val idx = bases.indexOf(base)
            if (idx >= 0) return edges[idx]
            bases += base
            return ArrayList<Edge>(2).also { edges += it }
        }

        private fun edge(from: InitialFactAp, to: InitialFactAp?) {
            val baseEdges = touch(from.base)
            val edge = Edge(from, to)
            if (edge !in baseEdges) baseEdges += edge
        }

        private fun filter(access: MethodFlowFunctionUtils.Access, type: JIRType?) {
            if (type == null) return
            filterBases += access.base
            filterTypes += type
        }

        fun assign(lhv: JIRValue, rhv: JIRExpr) {
            if (rhv is JIRBinaryExpr) {
                assign(lhv, rhv.lhv)
                assign(lhv, rhv.rhv)
                return
            }

            val from = when (rhv) {
                is JIRCastExpr -> MethodFlowFunctionUtils.mkAccess(rhv.operand)?.also { filter(it, rhv.type) } ?: return
                is JIRImmediate -> MethodFlowFunctionUtils.mkAccess(rhv)?.also { filter(it, rhv.type) } ?: return
                is JIRArrayAccess -> MethodFlowFunctionUtils.mkAccess(rhv)?.also { filter(it, rhv.array.type) } ?: return
                is JIRFieldRef -> MethodFlowFunctionUtils.mkAccess(rhv)
                    ?.also { filter(it, rhv.instance?.type) }
                    ?.also { filter(it, rhv.field.enclosingType) }
                    ?: return
                else -> null
            }

            val to = when (lhv) {
                is JIRImmediate -> MethodFlowFunctionUtils.mkAccess(lhv)?.also { filter(it, lhv.type) } ?: return
                is JIRArrayAccess -> MethodFlowFunctionUtils.mkAccess(lhv)?.also { filter(it, lhv.array.type) } ?: return
                is JIRFieldRef -> MethodFlowFunctionUtils.mkAccess(lhv)
                    ?.also { filter(it, lhv.instance?.type) }
                    ?.also { filter(it, lhv.field.enclosingType) }
                    ?: return
                else -> error("Assign to complex value: $lhv")
            }

            when {
                from is MethodFlowFunctionUtils.MemoryAccess -> {
                    check(to !is MethodFlowFunctionUtils.MemoryAccess) { "Complex assignment: $lhv = $rhv" }
                    read(to.base, from)
                }

                to is MethodFlowFunctionUtils.MemoryAccess -> write(to, from?.base)

                else -> move(to.base, from?.base)
            }
        }

        fun move(to: AccessPathBase, from: AccessPathBase?) {
            touch(to)
            if (from == null) return
            edge(fact(from), fact(from))
            if (from != to) edge(fact(from), fact(to))
        }

        private fun path(access: MethodFlowFunctionUtils.MemoryAccess): List<Accessor> = when (access) {
            is MethodFlowFunctionUtils.RefAccess -> listOf(access.accessor)
            is MethodFlowFunctionUtils.StaticRefAccess -> listOf(access.classStaticAccessor, access.accessor)
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

        private fun read(to: AccessPathBase, access: MethodFlowFunctionUtils.MemoryAccess) {
            val base = access.base
            val accessors = path(access)
            val source = fact(base, accessors)

            touch(to)
            if (base != to) {
                keepAllExcept(base, accessors)
                edge(source, source)
            } else {
                edge(fact(base).exclude(accessors.first()), null)
            }
            edge(source, fact(to))
        }

        private fun write(access: MethodFlowFunctionUtils.MemoryAccess, from: AccessPathBase?) {
            val base = access.base
            val accessors = path(access)

            if (accessors.first() is ElementAccessor) {
                edge(fact(base), fact(base))
            } else {
                keepAllExcept(base, accessors)
            }

            if (from != null) {
                if (from != base) edge(fact(from), fact(from))
                edge(fact(from), fact(base, accessors))
            }

            aliasAnalysis?.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
                if (aliasBase != base) {
                    val aliasPath = aliasAccessors + accessors
                    aliasPropagation(aliasBase, aliasPath)
                    if (from != null) edge(fact(from), fact(aliasBase, aliasPath))
                }
            }
        }
    }
}

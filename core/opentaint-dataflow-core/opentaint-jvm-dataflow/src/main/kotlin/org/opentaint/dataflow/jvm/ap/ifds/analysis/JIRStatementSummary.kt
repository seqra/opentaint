package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
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

class JIRStatementSummary(
    val edges: Map<AccessPathBase, List<Edge>>,
    val typeFilters: Map<AccessPathBase, List<JIRType>>,
) {
    data class Edge(val from: InitialFactAp, val to: InitialFactAp?)

    companion object {
        val Empty = JIRStatementSummary(emptyMap(), emptyMap())

        fun build(apManager: ApManager, inst: JIRInst, aliasAnalysis: JIRLocalAliasAnalysis?): JIRStatementSummary {
            val builder = Builder(inst, aliasAnalysis)
            val transfer = builder.build() ?: return Empty
            return JIRStatementSummary(transfer.toEdges(apManager), builder.typeFilters)
        }

        private val temporary = AccessPathBase.LocalVar.create(-1)
    }

    private data class Pattern(
        val base: AccessPathBase,
        val accessors: List<Accessor> = emptyList(),
        val exclusions: Set<Accessor> = emptySet(),
    ) {
        fun exclude(accessor: Accessor) = copy(exclusions = exclusions + accessor)
        fun append(rest: List<Accessor>) = copy(accessors = accessors + rest)

        fun toFact(apManager: ApManager): InitialFactAp {
            val path = accessors.foldRight(apManager.mostAbstractInitialAp(base)) { a, f -> f.prependAccessor(a) }
            return exclusions.fold(path) { f, a -> f.exclude(a) }
        }
    }

    private data class PatternEdge(val from: Pattern, val to: Pattern?)

    private class Transfer {
        val edges = linkedMapOf<AccessPathBase, LinkedHashSet<PatternEdge>>()

        fun touch(base: AccessPathBase) = edges.getOrPut(base) { linkedSetOf() }

        fun add(from: Pattern, to: Pattern?) {
            touch(from.base) += PatternEdge(from, to)
        }

        fun then(second: Transfer): Transfer {
            val result = Transfer()
            for ((base, firstEdges) in edges) {
                result.touch(base)
                for (edge in firstEdges) {
                    val to = edge.to
                    val secondEdges = to?.let { second.edges[it.base] }
                    if (secondEdges == null) {
                        result.add(edge.from, to)
                        continue
                    }

                    var matched = false
                    for (next in secondEdges) {
                        val composed = compose(edge.from, to, next) ?: continue
                        result.add(composed.from, composed.to)
                        matched = true
                    }

                    if (!matched && edge.from.exclusions.isNotEmpty()) {
                        result.add(edge.from, null)
                    }
                }
            }

            for ((base, secondEdges) in second.edges) {
                if (base in edges) continue
                result.touch(base)
                secondEdges.forEach { result.add(it.from, it.to) }
            }

            return result
        }

        private fun compose(a: Pattern, b: Pattern, next: PatternEdge): PatternEdge? {
            val c = next.from
            val d = next.to
            if (c.base != b.base) return null

            if (b.accessors.size >= c.accessors.size && b.accessors.subList(0, c.accessors.size) == c.accessors) {
                val rest = b.accessors.subList(c.accessors.size, b.accessors.size)
                if (rest.isNotEmpty() && rest.first() in c.exclusions) return null
                val from = if (rest.isEmpty()) a.copy(exclusions = a.exclusions + c.exclusions) else a
                return PatternEdge(from, d?.append(rest))
            }

            if (c.accessors.subList(0, b.accessors.size) == b.accessors) {
                val rest = c.accessors.subList(b.accessors.size, c.accessors.size)
                if (rest.first() in a.exclusions) return null
                return PatternEdge(a.append(rest).copy(exclusions = c.exclusions), d)
            }

            return null
        }

        fun eliminate(base: AccessPathBase): Transfer {
            val result = Transfer()
            for ((from, fromEdges) in edges) {
                if (from == base) continue
                result.touch(from)
                fromEdges.filter { it.to?.base != base }.forEach { result.add(it.from, it.to) }
            }
            return result
        }

        fun toEdges(apManager: ApManager): Map<AccessPathBase, List<Edge>> =
            edges.mapValues { (_, patternEdges) ->
                patternEdges.map { Edge(it.from.toFact(apManager), it.to?.toFact(apManager)) }
            }
    }

    private class Builder(
        private val inst: JIRInst,
        private val aliasAnalysis: JIRLocalAliasAnalysis?,
    ) {
        val typeFilters = hashMapOf<AccessPathBase, MutableList<JIRType>>()

        fun build(): Transfer? = when (inst) {
            is JIRAssignInst -> Transfer().also { assign(it, inst.lhv, inst.rhv) }
            is JIRReturnInst -> Transfer().also { move(it, AccessPathBase.Return, inst.returnValue?.let { v -> accessPathBase(v) }) }
            is JIRThrowInst -> Transfer().also { move(it, AccessPathBase.Exception, accessPathBase(inst.throwable)) }
            else -> null
        }

        private fun filter(access: MethodFlowFunctionUtils.Access, type: JIRType?) {
            if (type == null) return
            typeFilters.getOrPut(access.base) { mutableListOf() } += type
        }

        private fun assign(t: Transfer, lhv: JIRValue, rhv: JIRExpr) {
            if (rhv is JIRBinaryExpr) {
                assign(t, lhv, rhv.lhv)
                assign(t, lhv, rhv.rhv)
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
                    if (to.base != from.base) {
                        read(t, to.base, from)
                    } else {
                        val first = Transfer().also { read(it, temporary, from) }
                        val second = Transfer().also { move(it, to.base, temporary) }
                        first.then(second).eliminate(temporary).edges.forEach { (base, edges) ->
                            t.touch(base).addAll(edges)
                        }
                    }
                }

                to is MethodFlowFunctionUtils.MemoryAccess -> write(t, to, from?.base)

                else -> move(t, to.base, from?.base)
            }
        }

        private fun move(t: Transfer, to: AccessPathBase, from: AccessPathBase?) {
            t.touch(to)
            if (from == null) return
            t.add(Pattern(from), Pattern(from))
            if (from != to) t.add(Pattern(from), Pattern(to))
        }

        private fun path(access: MethodFlowFunctionUtils.MemoryAccess): List<Accessor> = when (access) {
            is MethodFlowFunctionUtils.RefAccess -> listOf(access.accessor)
            is MethodFlowFunctionUtils.StaticRefAccess -> listOf(access.classStaticAccessor, access.accessor)
        }

        private fun split(t: Transfer, base: AccessPathBase, accessors: List<Accessor>) {
            for (i in accessors.indices) {
                val prefix = Pattern(base, accessors.subList(0, i))
                t.add(prefix.exclude(accessors[i]), prefix)
            }
        }

        private fun aliases(t: Transfer, base: AccessPathBase, accessor: Accessor) {
            aliasAnalysis?.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
                t.add(Pattern(base).exclude(accessor), Pattern(aliasBase, aliasAccessors))
            }
        }

        private fun read(t: Transfer, to: AccessPathBase, access: MethodFlowFunctionUtils.MemoryAccess) {
            val accessors = path(access)
            val source = Pattern(access.base, accessors)

            t.touch(to)
            split(t, access.base, accessors)
            t.add(source, source)
            t.add(source, Pattern(to))
            aliases(t, access.base, accessors.first())
        }

        private fun write(t: Transfer, access: MethodFlowFunctionUtils.MemoryAccess, from: AccessPathBase?) {
            val base = access.base
            val accessors = path(access)
            val target = Pattern(base, accessors)

            if (accessors.first() is ElementAccessor) {
                t.add(Pattern(base), Pattern(base))
            } else {
                split(t, base, accessors)
                aliases(t, base, accessors.first())
            }

            if (from == null) return
            if (from != base) t.add(Pattern(from), Pattern(from))
            t.add(Pattern(from), target)
            aliasAnalysis?.forEachAliasPathAtStatement(inst, base) { aliasBase, aliasAccessors ->
                t.add(Pattern(from), Pattern(aliasBase, aliasAccessors + accessors))
            }
        }
    }
}

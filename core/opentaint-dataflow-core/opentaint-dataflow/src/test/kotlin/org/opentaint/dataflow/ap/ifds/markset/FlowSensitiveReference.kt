package org.opentaint.dataflow.ap.ifds.markset

import java.util.BitSet

/**
 * A slow, direct reading of the rules of `MarkScan/FlowSensitive.lean` and `MarkScan/Relevance.lean`,
 * for tests: `PtReach` and `InFS` as one naive fixpoint over every `(root, node, pc)`, then
 * `ApplicableFS` (via `CubeSatFS`) and `NeededOver ApplicableFS`. Nodes are methods.
 */
internal object FlowSensitiveReference {
    class Result(val applicable: Set<Int>, val needed: Set<Int>, val rootMarks: Map<Int, Set<Int>>)

    fun run(p: MarkSetProgram): Result {
        val cfg = checkNotNull(p.cfg)
        val roots = p.roots.distinct()
        val n = p.methodCount
        val reach = roots.associateWith { Array(n) { BooleanArray(cfg.stmtCount[it]) } }
        val inFs = roots.associateWith { Array(n) { m -> Array(cfg.stmtCount[m]) { BitSet() } } }
        val sitesAt = Array(n) { m -> Array(cfg.stmtCount[m]) { mutableListOf<Int>() } }
        for ((i, site) in p.sites.withIndex()) sitesAt[site.method][cfg.siteStmt[i]] += i

        fun union(m: Int, s: Int): BitSet? {
            var u: BitSet? = null
            for (e in roots) {
                if (!reach.getValue(e)[m][s]) continue
                u = (u ?: BitSet()).apply { or(inFs.getValue(e)[m][s]) }
            }
            return u
        }

        fun add(target: BitSet, marks: BitSet): Boolean {
            val before = target.cardinality()
            target.or(marks)
            return target.cardinality() != before
        }

        var changed = true
        while (changed) {
            changed = false
            for (e in roots) {
                val r = reach.getValue(e)
                val x = inFs.getValue(e)
                if (!r[e][cfg.entry[e]]) { r[e][cfg.entry[e]] = true; changed = true }
                for (m in 0 until n) for (s in 0 until cfg.stmtCount[m]) {
                    if (!r[m][s]) continue
                    for (t in cfg.succ[m][s]) {
                        if (!r[m][t]) { r[m][t] = true; changed = true }
                        changed = add(x[m][t], x[m][s]) || changed // flow
                    }
                    for (c in cfg.callsAt[m][s]) {
                        val ce = cfg.entry[c]
                        if (!r[c][ce]) { r[c][ce] = true; changed = true }
                        changed = add(x[c][ce], x[m][s]) || changed // callIn
                        for (ex in cfg.exits[c]) for (t in cfg.succ[m][s]) {
                            changed = add(x[m][t], x[c][ex]) || changed // ret
                        }
                    }
                    for (i in sitesAt[m][s]) {
                        val site = p.sites[i]
                        val gens = BitSet().apply { site.gens.forEach { set(it) } }
                        if (site.cond.eval(x[m][s]).smallSat) changed = add(x[m][s], gens) || changed // single
                        val u = union(m, s) ?: continue
                        val eval = site.cond.eval(u)
                        if (eval.big) changed = add(x[m][s], gens) || changed // joined
                        if (site.kind == SiteKind.SINK && eval.sat) changed = add(x[m][s], gens) || changed // sinkGen
                    }
                }
            }
        }

        val applicable = p.sites.indices.filter { i ->
            val site = p.sites[i]
            val m = site.method
            val s = cfg.siteStmt[i]
            val small = roots.any { e -> reach.getValue(e)[m][s] && site.cond.eval(inFs.getValue(e)[m][s]).smallSat }
            small || union(m, s)?.let { site.cond.eval(it).big } == true
        }.toSet()

        val needed = BitSet().apply { or(p.cleanerAtoms) }
        for (i in applicable) {
            val site = p.sites[i]
            when (site.kind) {
                SiteKind.SINK -> { site.cond.atoms(needed); site.gens.forEach { needed.set(it) } }
                SiteKind.PASS_THROUGH -> site.cond.atoms(needed)
                SiteKind.SOURCE -> Unit
            }
        }
        var grew = true
        while (grew) {
            grew = false
            for (i in applicable) {
                val site = p.sites[i]
                if (site.gens.none { needed.get(it) }) continue
                grew = add(needed, site.cond.atoms()) || grew
            }
        }

        val rootMarks = roots.associateWith { e ->
            val all = BitSet()
            inFs.getValue(e).forEach { stmts -> stmts.forEach { all.or(it) } }
            all.stream().toArray().toSet()
        }
        return Result(applicable, needed.stream().toArray().toSet(), rootMarks)
    }
}

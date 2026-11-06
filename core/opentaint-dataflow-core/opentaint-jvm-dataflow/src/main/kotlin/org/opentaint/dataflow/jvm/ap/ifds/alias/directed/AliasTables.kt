package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/**
 * The tables of one method analysis. All states of the method share them.
 *
 * @param symDepth K: the maximal path length of a symbolic origin (spec §3, §7).
 */
class AliasTables(val symDepth: Int) {
    val cells = CellTable()
    val vars = VarTable()
    val sites = SiteTable()
    val bases = BaseTable()
    val nodes = NodeTable()
    val origins = OriginTable(symDepth, bases, nodes, sites)

    /** Makes all tables read-only. Run it after the fixpoint, before the queries (IMPL §6.4). */
    fun freeze() {
        cells.freeze()
        vars.freeze()
        sites.freeze()
        bases.freeze()
        nodes.freeze()
        origins.freeze()
    }
}

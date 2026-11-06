package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasInstr.ArrayLoad
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasInstr.ArrayStore
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasInstr.Assign
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasInstr.FieldLoad
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasInstr.FieldStore
import org.opentaint.dataflow.jvm.ap.ifds.alias.directed.AliasInstr.StaticRead

/**
 * A small test driver for the engine core. It runs the transfer on a list of instructions.
 * It has no CFG.
 */
class DirectedEngineFixture(symDepth: Int = 7) {
    val tables = AliasTables(symDepth)
    val transfer = AliasTransfer(tables)
    val origins get() = tables.origins
    val bases get() = tables.bases
    val nodes get() = tables.nodes

    fun field(name: String): CellId = tables.cells.field("C", name, "java.lang.Object")
    fun local(i: Int): AliasValue.Local = AliasValue.Local(tables.vars.local(i))
    fun arg(i: Int): AliasValue.Arg = AliasValue.Arg(i)
    fun site(i: Int): SiteId = tables.sites.site(i)
    fun loopSite(i: Int): SiteId = tables.sites.site(i).also { tables.sites.markLoopSite(it) }

    fun run(vararg instrs: AliasInstr, from: AliasState = AliasState.EMPTY): AliasState =
        instrs.fold(from) { st, instr -> transfer.transfer(st, instr) }

    // Instructions.
    fun assign(dst: AliasValue.Local, value: AliasValue) = Assign(dst.v, value)
    fun load(dst: AliasValue.Local, base: AliasValue.Ref, cell: CellId) = FieldLoad(dst.v, base, cell)
    fun aload(dst: AliasValue.Local, base: AliasValue.Ref) = ArrayLoad(dst.v, base)
    fun store(base: AliasValue.Ref, cell: CellId, value: AliasValue) = FieldStore(base, cell, value)
    fun astore(base: AliasValue.Ref, value: AliasValue) = ArrayStore(base, value)
    fun staticRead(dst: AliasValue.Local, className: String, cell: CellId) =
        StaticRead(dst.v, bases.static(className), cell)

    // Origins.
    fun argO(i: Int): OriginId = origins.root(bases.arg(i))
    fun thisO(): OriginId = origins.root(bases.thisBase())
    fun path(root: OriginId, vararg cells: CellId): OriginId = cells.fold(root) { o, c -> origins.child(o, c) }

    // Views.
    fun pts(st: AliasState, v: AliasValue.Ref): Set<OriginId> = nodes.members(transfer.valueNode(st, v)).toSet()
    fun cell(st: AliasState, o: OriginId, c: CellId): Set<OriginId> = nodes.members(transfer.read(st, o, c)).toSet()
    fun set(vararg o: OriginId): Set<OriginId> = o.toSet()
    fun node(vararg o: OriginId): NodeId = nodes.of(*o)

    fun withSets(st: AliasState, etree: NodeId, eval: NodeId): AliasState =
        st.edit().apply { setVar(ETREE, etree); setVar(EVAL, eval) }.build()
}

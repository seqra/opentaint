package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

import kotlin.random.Random

/**
 * A seeded random alias CFG for the oracles of IMPL §9.1 (items 2 and 4).
 *
 * - Locals 0..4, fields 0..1 and the array cell, allocation sites 0..3, fresh sites 0..3 (unknown
 *   expressions, call results and catch variables share them), one null site for each null
 *   statement, two string constants, one static holder, `this` and two arguments.
 * - Statements: copies, roots, `new`, unknown expressions, nulls, constants, field and array loads
 *   and stores, static reads, unresolved calls (with or without a result, with up to three
 *   arguments), and `throw` in a `try` block.
 * - Blocks: sequences, branches, loops and `try` blocks with a handler, nested up to depth 3.
 *   Each node of a `try` block is a thrower of its handlers (and of the outer handlers). A handler
 *   starts with a catch (`{Sym(FRESH(s))}`).
 * - Some sequences have a shape of the call examples of the spec ([shape]).
 * - Some programs get an extra edge between two random nodes (irreducible graphs, loops at the
 *   entry, unreachable nodes).
 * - [assignedPrefix]: most programs assign each local at the entry, so each local is assigned
 *   before its use (A4). The other programs can read an unassigned local.
 * - The exit node reads each local, so the queries at the exit see each local. Some nodes read
 *   one more local (other live sets).
 *
 * K ([k]) is 0, 1 or 2.
 */
class RandomAliasProgram(val seed: Long) {
    private val rnd = Random(seed)
    val k: Int = rnd.nextInt(3)
    val tables = AliasTables(k)
    val locals = IntArray(LOCALS) { tables.vars.local(it) }
    private val fields = IntArray(FIELDS) { tables.cells.field("R", "f$it", "java.lang.Object") }
    private val allocSites = IntArray(SITES) { tables.sites.site(it) }
    private val freshSites = IntArray(SITES) { tables.sites.site(100 + it) }
    private var nextNullSite = 1000
    private val consts = intArrayOf(tables.bases.const(STRING_TYPE, "a"), tables.bases.const(STRING_TYPE, "b"))
    private val staticBase = tables.bases.static("R\$S")

    val assignedPrefix: Boolean = rnd.nextInt(10) < 8

    private class MNode(val instr: AliasInstr, val exc: IntArray) {
        val succ = ArrayList<Int>()
        val uses = ArrayList<Int>()
    }

    private class Frag(val entry: Int, val exits: List<Int>)

    private val nodes = ArrayList<MNode>()

    /** The exit node: it reads each local. */
    val exit: Int
    val cfg: AliasCfg

    init {
        var entry: Int
        var exits: List<Int>
        if (assignedPrefix) {
            entry = add(initial(0), NO_NODES)
            var last = entry
            for (i in 1 until LOCALS) {
                val n = add(initial(i), NO_NODES)
                nodes[last].succ += n
                last = n
            }
            val body = block(0, NO_NODES)
            nodes[last].succ += body.entry
            exits = body.exits
        } else {
            val body = block(0, NO_NODES)
            entry = body.entry
            exits = body.exits
        }
        exit = add(AliasInstr.Nop, NO_NODES)
        nodes[exit].uses += locals.toList()
        for (e in exits) nodes[e].succ += exit
        if (rnd.nextInt(10) < 2) {
            val from = rnd.nextInt(nodes.size)
            val to = rnd.nextInt(nodes.size)
            if (from != exit) nodes[from].succ += to
        }
        for (n in nodes) if (rnd.nextInt(10) == 0) n.uses += locals[rnd.nextInt(LOCALS)]
        cfg = AliasCfg.direct(
            tables,
            nodes.map { AliasCfg.Node(it.instr, it.succ.distinct().toIntArray(), it.exc, it.uses.distinct().toIntArray()) },
            entry,
        )
    }

    /** A readable text of the program (for a failure message). */
    fun text(): String = buildString {
        append("seed=$seed K=$k entry=${cfg.entry} exit=$exit\n")
        for (v in 0 until cfg.size) {
            append("  $v: ${cfg.instr(v)} -> ${cfg.successors(v).toList()}")
            if (cfg.handlers(v).isNotEmpty()) append(" exc ${cfg.handlers(v).toList()}")
            append('\n')
        }
    }

    private fun add(instr: AliasInstr, handlers: IntArray): Int {
        nodes += MNode(instr, handlers)
        return nodes.size - 1
    }

    private fun local(): Int = locals[rnd.nextInt(LOCALS)]

    private fun initial(i: Int): AliasInstr = AliasInstr.Assign(
        locals[i],
        when (rnd.nextInt(5)) {
            0 -> AliasValue.Arg(rnd.nextInt(2))
            1 -> AliasValue.New(allocSites[rnd.nextInt(SITES)])
            2 -> AliasValue.Null(tables.sites.site(nextNullSite++))
            3 -> AliasValue.Const(consts[rnd.nextInt(2)])
            else -> AliasValue.Fresh(freshSites[rnd.nextInt(SITES)])
        },
    )

    private fun ref(): AliasValue.Ref = when (rnd.nextInt(10)) {
        0 -> AliasValue.Arg(rnd.nextInt(2))
        1 -> AliasValue.This
        else -> AliasValue.Local(local())
    }

    private fun stored(): AliasValue = when (rnd.nextInt(10)) {
        0 -> AliasValue.Null(tables.sites.site(nextNullSite++))
        1 -> AliasValue.Const(consts[rnd.nextInt(2)])
        2 -> AliasValue.New(allocSites[rnd.nextInt(SITES)])
        else -> ref()
    }

    private fun arg(): AliasValue = when (rnd.nextInt(8)) {
        0 -> AliasValue.Null(tables.sites.site(nextNullSite++))
        1 -> AliasValue.Const(consts[rnd.nextInt(2)])
        else -> ref()
    }

    private fun field(): CellId = fields[rnd.nextInt(FIELDS)]

    private fun stmt(): AliasInstr = when (rnd.nextInt(16)) {
        0 -> AliasInstr.Assign(local(), AliasValue.Local(local()))
        1 -> AliasInstr.Assign(local(), ref())
        2 -> AliasInstr.Assign(local(), AliasValue.New(allocSites[rnd.nextInt(SITES)]))
        3 -> AliasInstr.Assign(local(), AliasValue.Fresh(freshSites[rnd.nextInt(SITES)]))
        4 -> AliasInstr.Assign(local(), AliasValue.Null(tables.sites.site(nextNullSite++)))
        5 -> AliasInstr.Assign(local(), AliasValue.Const(consts[rnd.nextInt(2)]))
        6, 7 -> AliasInstr.FieldLoad(local(), ref(), field())
        8, 9 -> AliasInstr.FieldStore(ref(), field(), stored())
        10 -> AliasInstr.ArrayLoad(local(), ref())
        11 -> AliasInstr.ArrayStore(ref(), stored())
        12, 13 -> AliasInstr.UnresolvedCall(
            freshSites[rnd.nextInt(SITES)],
            if (rnd.nextBoolean()) local() else null,
            List(rnd.nextInt(4)) { arg() },
        )
        14 -> AliasInstr.StaticRead(local(), staticBase, field())
        else -> AliasInstr.Nop
    }

    private fun block(depth: Int, handlers: IntArray): Frag {
        val r = rnd.nextInt(10)
        return when {
            depth >= MAX_DEPTH || r < 4 -> sequence(depth, handlers)
            r < 6 -> branch(depth, handlers)
            r < 8 -> loop(depth, handlers)
            else -> tryBlock(depth, handlers)
        }
    }

    private fun sequence(depth: Int, handlers: IntArray): Frag {
        val n = 2 + rnd.nextInt(4)
        var entry = -1
        var exits = emptyList<Int>()
        for (i in 0 until n) {
            val f = if (depth < MAX_DEPTH && rnd.nextInt(3) == 0) block(depth + 1, handlers) else single(handlers)
            if (entry < 0) entry = f.entry else for (e in exits) nodes[e].succ += f.entry
            exits = f.exits
            if (exits.isEmpty()) break
        }
        return Frag(entry, exits)
    }

    /**
     * A shape of the spec examples of the call (§5.6, §6.7) with random locals: a value read before
     * the call, a store before the call, and a strong-update candidate after it. Random statements
     * seldom make these shapes, and they test `Etree` and `Eval`.
     */
    private fun shape(handlers: IntArray): Frag {
        val (x, z, e, t, v) = List(5) { local() }
        val f = field()
        val g = field()
        val call = AliasInstr.UnresolvedCall(freshSites[rnd.nextInt(SITES)], null, listOf(AliasValue.Local(x)))
        val instrs = when (rnd.nextInt(3)) {
            // z = new; z.g = e; x.f = z; m(x); t = x.f; t.g = v
            0 -> listOf(
                AliasInstr.Assign(z, AliasValue.New(allocSites[rnd.nextInt(SITES)])),
                AliasInstr.FieldStore(AliasValue.Local(z), g, AliasValue.Local(e)),
                AliasInstr.FieldStore(AliasValue.Local(x), f, AliasValue.Local(z)),
                call,
                AliasInstr.FieldLoad(t, AliasValue.Local(x), f),
                AliasInstr.FieldStore(AliasValue.Local(t), g, AliasValue.Local(v)),
            )
            // w = x.f; e = w.g; m(x); t = x.f; t.g = v
            1 -> listOf(
                AliasInstr.FieldLoad(z, AliasValue.Local(x), f),
                AliasInstr.FieldLoad(e, AliasValue.Local(z), g),
                call,
                AliasInstr.FieldLoad(t, AliasValue.Local(x), f),
                AliasInstr.FieldStore(AliasValue.Local(t), g, AliasValue.Local(v)),
            )
            // t = x.f; m(x); t.g = v (L1); then a read through x
            else -> listOf(
                AliasInstr.FieldLoad(t, AliasValue.Local(x), f),
                call,
                AliasInstr.FieldStore(AliasValue.Local(t), g, AliasValue.Local(v)),
                AliasInstr.FieldLoad(e, AliasValue.Local(x), f),
            )
        }
        val ids = instrs.map { add(it, handlers) }
        for (i in 1 until ids.size) nodes[ids[i - 1]].succ += ids[i]
        return Frag(ids.first(), listOf(ids.last()))
    }

    private fun single(handlers: IntArray): Frag {
        if (rnd.nextInt(12) == 0) return shape(handlers)
        if (handlers.isNotEmpty() && rnd.nextInt(10) == 0) {
            return Frag(add(AliasInstr.Throw(AliasValue.Local(local())), handlers), emptyList())
        }
        val n = add(stmt(), handlers)
        return Frag(n, listOf(n))
    }

    private fun branch(depth: Int, handlers: IntArray): Frag {
        val b = add(AliasInstr.Nop, handlers)
        val x = block(depth + 1, handlers)
        nodes[b].succ += x.entry
        if (rnd.nextBoolean()) return Frag(b, x.exits + b)
        val y = block(depth + 1, handlers)
        nodes[b].succ += y.entry
        return Frag(b, x.exits + y.exits)
    }

    private fun loop(depth: Int, handlers: IntArray): Frag {
        val head = add(AliasInstr.Nop, handlers)
        val body = block(depth + 1, handlers)
        nodes[head].succ += body.entry
        for (e in body.exits) nodes[e].succ += head
        return Frag(head, listOf(head))
    }

    private fun tryBlock(depth: Int, handlers: IntArray): Frag {
        val h = add(AliasInstr.Assign(local(), AliasValue.Fresh(freshSites[rnd.nextInt(SITES)])), handlers)
        val body = block(depth + 1, handlers + h)
        val after = block(depth + 1, handlers)
        nodes[h].succ += after.entry
        return Frag(body.entry, body.exits + after.exits)
    }

    companion object {
        const val LOCALS = 5
        const val FIELDS = 2
        const val SITES = 4
        const val MAX_DEPTH = 3
        private val NO_NODES = IntArray(0)
    }
}

package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/*
 * The Lean test vectors of design VS (IMPL §9.1 item 1): the line format of
 * `formal/directed-alias/Export/Vectors.lean`, its parser, and the translation of a Lean program
 * to an engine CFG.
 */

/** A cell of a Lean path: field `f`, or [LEAN_ELEM] for an array element. */
const val LEAN_ELEM: Int = -1

/** A statement of the Lean IR (`DirectedAlias/Syntax.lean`, `Stmt`). */
sealed interface LStmt {
    data class New(val x: Int, val s: Int) : LStmt
    data class Null(val x: Int) : LStmt
    data class Copy(val x: Int, val y: Int) : LStmt
    data class Load(val x: Int, val y: Int, val f: Int) : LStmt
    data class Store(val x: Int, val f: Int, val y: Int) : LStmt
    data class ALoad(val x: Int, val y: Int) : LStmt
    data class AStore(val x: Int, val y: Int) : LStmt
    data class Unknown(val x: Int, val s: Int) : LStmt
    data class Call(val ret: Int?, val s: Int, val args: List<Int>) : LStmt
}

/** A structured Lean program (`Prog`). */
sealed interface LProg {
    data object Skip : LProg
    data class St(val st: LStmt) : LProg
    data class Seq(val p: LProg, val q: LProg) : LProg
    data class Choice(val p: LProg, val q: LProg) : LProg
    data class Loop(val p: LProg) : LProg
}

/** An instruction of a Lean CFG node (`Impl/Cfg.lean`, `Instr`). */
sealed interface LInstr {
    data class St(val st: LStmt) : LInstr
    data object Nop : LInstr
    data class Thr(val y: Int) : LInstr
    data class Cat(val x: Int, val s: Int) : LInstr
    data class Cnst(val x: Int, val s: Int) : LInstr
}

data class LNode(val instr: LInstr, val succ: List<Int>, val exc: List<Int>, val kills: List<Int>)

data class LCfg(val entry: Int, val nodes: List<LNode>)

/** A Lean access path: a variable and its cells. */
data class LPath(val v: Int, val cells: List<Int>) {
    override fun toString(): String = v.toString() + cells.joinToString("") { if (it == LEAN_ELEM) ".*" else ".$it" }
}

/**
 * One line of the vector file. A `V` line has [q] and [may]. An `F` line has [variable], [depth],
 * [paths] and [plain]. A structured program has [prog]; a CFG example has [cfg] and [node].
 */
data class LeanVector(
    val kind: Char,
    val name: String,
    val k: Int,
    val entryUnique: Boolean,
    val statics: List<Int>,
    val frame: List<Pair<Int, Int>>,
    val prog: LProg?,
    val cfg: LCfg?,
    val node: Int?,
    val q: Pair<LPath, LPath>?,
    val may: Boolean?,
    val variable: Int?,
    val depth: Int?,
    val paths: Set<String>?,
    val plain: Set<String>?,
    val line: String,
)

/** The parser of the vector lines. */
object LeanVectorParser {
    fun parseFile(text: String): List<LeanVector> =
        text.lines().filter { it.isNotBlank() && !it.startsWith("#") }.map(::parseLine)

    fun parseLine(line: String): LeanVector {
        val parts = line.split(" | ")
        val head = parts[0]
        val kind = head[0]
        require(kind == 'V' || kind == 'F') { "Unknown line kind: $line" }
        val name = head.substring(2)
        val fields = HashMap<String, String>()
        for (p in parts.drop(1)) {
            for (item in if (p.startsWith("K=")) p.split(" ") else listOf(p)) {
                val eq = item.indexOf('=')
                require(eq > 0) { "Bad field '$item' in $line" }
                fields[item.substring(0, eq)] = item.substring(eq + 1)
            }
        }
        require(fields["hv"] == "vs" && fields["rec"] == "1") { "Only hv=vs rec=1 vectors: $line" }
        return LeanVector(
            kind = kind,
            name = name,
            k = fields.getValue("K").toInt(),
            entryUnique = fields.getValue("eu") == "1",
            statics = ints(fields.getValue("statics")),
            frame = fields.getValue("frame").split(',').filter { it.isNotEmpty() }.map {
                val (x, r) = it.split(':')
                x.toInt() to r.toInt()
            },
            prog = fields["prog"]?.let { prog(SExpr.parse(it)) },
            cfg = fields["cfg"]?.let { cfg(SExpr.parse(it)) },
            node = fields["at"]?.toInt(),
            q = fields["q"]?.let { q ->
                val (a, b) = q.split('~')
                path(a) to path(b)
            },
            may = fields["may"]?.toBooleanStrict(),
            variable = fields["var"]?.toInt(),
            depth = fields["D"]?.toInt(),
            paths = fields["paths"]?.let(::pathSet),
            plain = fields["plain"]?.let(::pathSet),
            line = line,
        )
    }

    private fun ints(s: String): List<Int> = s.split(',').filter { it.isNotEmpty() }.map { it.toInt() }

    private fun pathSet(s: String): Set<String> = s.split(',').filter { it.isNotEmpty() }.toSet()

    fun path(s: String): LPath {
        val parts = s.split('.')
        return LPath(parts[0].toInt(), parts.drop(1).map { if (it == "*") LEAN_ELEM else it.toInt() })
    }

    private fun stmt(e: SExpr.L): LStmt {
        val a = e.items
        fun n(i: Int) = (a[i] as SExpr.A).text.toInt()
        return when ((a[0] as SExpr.A).text) {
            "new" -> LStmt.New(n(1), n(2))
            "null" -> LStmt.Null(n(1))
            "copy" -> LStmt.Copy(n(1), n(2))
            "load" -> LStmt.Load(n(1), n(2), n(3))
            "store" -> LStmt.Store(n(1), n(2), n(3))
            "aload" -> LStmt.ALoad(n(1), n(2))
            "astore" -> LStmt.AStore(n(1), n(2))
            "unknown" -> LStmt.Unknown(n(1), n(2))
            "call" -> {
                val r = (a[1] as SExpr.A).text
                LStmt.Call(if (r == "_") null else r.toInt(), n(2), (3 until a.size).map(::n))
            }
            else -> error("Unknown statement: $e")
        }
    }

    private fun prog(e: SExpr): LProg = when {
        e is SExpr.A && e.text == "skip" -> LProg.Skip
        e is SExpr.L -> when ((e.items[0] as SExpr.A).text) {
            "seq" -> LProg.Seq(prog(e.items[1]), prog(e.items[2]))
            "choice" -> LProg.Choice(prog(e.items[1]), prog(e.items[2]))
            "loop" -> LProg.Loop(prog(e.items[1]))
            else -> LProg.St(stmt(e))
        }
        else -> error("Bad program: $e")
    }

    private fun instr(e: SExpr.L): LInstr {
        fun n(i: Int) = (e.items[i] as SExpr.A).text.toInt()
        return when ((e.items[0] as SExpr.A).text) {
            "nop" -> LInstr.Nop
            "thr" -> LInstr.Thr(n(1))
            "cat" -> LInstr.Cat(n(1), n(2))
            "cnst" -> LInstr.Cnst(n(1), n(2))
            else -> LInstr.St(stmt(e))
        }
    }

    private fun cfg(e: SExpr): LCfg {
        val items = (e as SExpr.L).items
        require((items[0] as SExpr.A).text == "cfg")
        val entry = (items[1] as SExpr.A).text.toInt()
        val nodes = items.drop(2).map { n ->
            val ni = (n as SExpr.L).items
            require((ni[0] as SExpr.A).text == "node")
            fun list(x: SExpr) = (x as SExpr.L).items.map { (it as SExpr.A).text.toInt() }
            LNode(instr(ni[1] as SExpr.L), list(ni[2]), list(ni[3]), list(ni[4]))
        }
        return LCfg(entry, nodes)
    }
}

/** An s-expression of the vector file. */
sealed interface SExpr {
    data class A(val text: String) : SExpr {
        override fun toString() = text
    }

    data class L(val items: List<SExpr>) : SExpr {
        override fun toString() = items.joinToString(" ", "(", ")")
    }

    companion object {
        fun parse(s: String): SExpr {
            val tokens = Regex("""\(|\)|[^\s()]+""").findAll(s).map { it.value }.toList()
            var pos = 0
            fun read(): SExpr {
                val t = tokens[pos++]
                if (t != "(") return A(t)
                val items = ArrayList<SExpr>()
                while (tokens[pos] != ")") items += read()
                pos++
                return L(items)
            }
            val e = read()
            require(pos == tokens.size) { "Trailing tokens in $s" }
            return e
        }
    }
}

/**
 * The engine run of one vector (the translation of IMPL §9.1 item 1).
 *
 * - A Lean variable `n` is the local `n` of the root context. A Lean field `f` is a field cell.
 * - The frame binds a variable to the root value of an argument (`Sym(ARG(r))`), or of a static
 *   holder (`Sym(STATIC(Sr))`) if `r` is a static root. The bindings are the initial state.
 * - A Lean site `s` is one engine site for each Lean site: two statements of one Lean site share
 *   the engine site, as in Lean (`onceB`). Each `null` statement has its own site (its null
 *   site in program order).
 * - `cat x s` is the catch of the engine (`{Sym(FRESH(s))}`, I2). `cnst x s` is a constant of the
 *   key `s` (`{Sym(CONST(s))}`, never unique; the vectors use the constant guard of Lean).
 * - Each node reads each variable of the vector ([AliasCfg.Node.extraUses]). So the kills remove
 *   no variable, as in Lean: the structured programs and the CFG examples of the vectors have
 *   no kills.
 * - A structured program is a CFG: a `choice` is a branch node and a join of its exits; a `loop`
 *   is a head node with an edge into the body and an edge out; the body exits go back to the head.
 *   The last node is an exit node. A `V` query of a program reads the state before the exit node.
 */
class LeanEngineRun(val vector: LeanVector) {
    val driver = DirectedTestDriver(symDepth = vector.k, maxAccessors = vector.depth ?: 2)
    private val tables = driver.tables
    private val fieldCells = HashMap<Int, CellId>()
    private var nullSites = 0
    private val allVars: IntArray = collectVars().sorted().toIntArray()
    private val engineVars: IntArray = allVars.map { tables.vars.local(it) }.toIntArray()
    private val nodes = ArrayList<AliasCfg.Node>()

    val cfg: AliasCfg
    val queryNode: Int
    val initial: AliasState

    init {
        if (vector.cfg != null) {
            for (n in vector.cfg.nodes) {
                nodes += AliasCfg.Node(
                    instr(n.instr), n.succ.toIntArray(), n.exc.toIntArray(), extraUses = engineVars,
                )
            }
            cfg = driver.cfg(nodes, vector.cfg.entry)
            queryNode = vector.node!!
        } else {
            val exit = compile(vector.prog!!)
            val end = add(AliasInstr.Nop)
            for (e in exit.exits) link(e, end)
            cfg = driver.cfg(nodes, exit.entry)
            queryNode = end
        }
        val values = HashMap<VarId, IntArray>()
        for ((x, r) in vector.frame) {
            val v = tables.vars.local(x)
            if (v in values) continue // the first binding wins (Lean `Frame.root?`)
            val base = if (r in vector.statics) tables.bases.static("lean.S$r") else tables.bases.arg(r)
            values[v] = intArrayOf(tables.origins.root(base))
        }
        initial = driver.stateWith(values)
    }

    /** The engine cell of a Lean cell. */
    fun cell(f: Int): CellId =
        if (f == LEAN_ELEM) ELEM_CELL else fieldCells.getOrPut(f) { tables.cells.field("lean.C", "f$f", "java.lang.Object") }

    /** The Lean path text of an engine path from a local. */
    fun leanPath(v: VarId, cells: List<CellId>): String {
        val x = tables.vars.key(v)!!.index
        val inv = fieldCells.entries.associate { (f, c) -> c to f }
        return x.toString() + cells.joinToString("") { if (it == ELEM_CELL) ".*" else ".${inv.getValue(it)}" }
    }

    fun local(x: Int): AliasValue.Local = AliasValue.Local(tables.vars.local(x))

    /** True if a statement reads a variable that the frame does not bind and no statement writes (A4 fails). */
    fun readsUnassigned(): Boolean {
        val stmts = vector.prog?.let { stmts(it) } ?: vector.cfg!!.nodes.mapNotNull { (it.instr as? LInstr.St)?.st }
        val defined = vector.frame.map { it.first }.toMutableSet()
        stmts.forEach { defined += defs(it) }
        vector.cfg?.nodes?.forEach { n ->
            when (val i = n.instr) {
                is LInstr.Cat -> defined += i.x
                is LInstr.Cnst -> defined += i.x
                else -> Unit
            }
        }
        return stmts.any { st -> uses(st).any { it !in defined } }
    }

    private class Frag(val entry: Int, val exits: List<Int>)

    private fun add(instr: AliasInstr): Int {
        nodes += AliasCfg.Node(instr, extraUses = engineVars)
        return nodes.size - 1
    }

    private fun link(from: Int, to: Int) {
        val n = nodes[from]
        nodes[from] = AliasCfg.Node(n.instr, n.succ + to, n.exc, n.extraUses, n.extraDefs)
    }

    private fun compile(p: LProg): Frag = when (p) {
        LProg.Skip -> add(AliasInstr.Nop).let { Frag(it, listOf(it)) }
        is LProg.St -> add(stmt(p.st)).let { Frag(it, listOf(it)) }
        is LProg.Seq -> {
            val a = compile(p.p)
            val b = compile(p.q)
            for (e in a.exits) link(e, b.entry)
            Frag(a.entry, b.exits)
        }
        is LProg.Choice -> {
            val branch = add(AliasInstr.Nop)
            val a = compile(p.p)
            val b = compile(p.q)
            link(branch, a.entry)
            link(branch, b.entry)
            Frag(branch, a.exits + b.exits)
        }
        is LProg.Loop -> {
            val head = add(AliasInstr.Nop)
            val body = compile(p.p)
            link(head, body.entry)
            for (e in body.exits) link(e, head)
            Frag(head, listOf(head))
        }
    }

    private fun site(s: Int): SiteId = tables.sites.site(LEAN_SITE + s)

    private fun stmt(st: LStmt): AliasInstr = when (st) {
        is LStmt.New -> AliasInstr.Assign(local(st.x).v, AliasValue.New(site(st.s)))
        is LStmt.Null -> AliasInstr.Assign(local(st.x).v, AliasValue.Null(tables.sites.site(NULL_SITE + nullSites++)))
        is LStmt.Copy -> AliasInstr.Assign(local(st.x).v, local(st.y))
        is LStmt.Load -> AliasInstr.FieldLoad(local(st.x).v, local(st.y), cell(st.f))
        is LStmt.Store -> AliasInstr.FieldStore(local(st.x), cell(st.f), local(st.y))
        is LStmt.ALoad -> AliasInstr.ArrayLoad(local(st.x).v, local(st.y))
        is LStmt.AStore -> AliasInstr.ArrayStore(local(st.x), local(st.y))
        is LStmt.Unknown -> AliasInstr.Assign(local(st.x).v, AliasValue.Fresh(site(st.s)))
        is LStmt.Call -> AliasInstr.UnresolvedCall(site(st.s), st.ret?.let { local(it).v }, st.args.map { local(it) })
    }

    private fun instr(i: LInstr): AliasInstr = when (i) {
        is LInstr.St -> stmt(i.st)
        LInstr.Nop -> AliasInstr.Nop
        is LInstr.Thr -> AliasInstr.Throw(local(i.y))
        is LInstr.Cat -> AliasInstr.Assign(local(i.x).v, AliasValue.Fresh(site(i.s)))
        is LInstr.Cnst -> AliasInstr.Assign(local(i.x).v, AliasValue.Const(tables.bases.const("lean.Const", "${i.s}")))
    }

    private fun collectVars(): Set<Int> {
        val out = HashSet<Int>()
        vector.frame.forEach { out += it.first }
        vector.q?.let { out += it.first.v; out += it.second.v }
        vector.variable?.let { out += it }
        val stmts = vector.prog?.let { stmts(it) } ?: vector.cfg!!.nodes.mapNotNull { (it.instr as? LInstr.St)?.st }
        stmts.forEach { out += uses(it); out += defs(it) }
        vector.cfg?.nodes?.forEach { n ->
            when (val i = n.instr) {
                is LInstr.Thr -> out += i.y
                is LInstr.Cat -> out += i.x
                is LInstr.Cnst -> out += i.x
                else -> Unit
            }
            out += n.kills
        }
        return out
    }

    private companion object {
        const val LEAN_SITE = 1000
        const val NULL_SITE = 100_000

        fun stmts(p: LProg): List<LStmt> = when (p) {
            LProg.Skip -> emptyList()
            is LProg.St -> listOf(p.st)
            is LProg.Seq -> stmts(p.p) + stmts(p.q)
            is LProg.Choice -> stmts(p.p) + stmts(p.q)
            is LProg.Loop -> stmts(p.p)
        }

        fun uses(st: LStmt): List<Int> = when (st) {
            is LStmt.New, is LStmt.Null, is LStmt.Unknown -> emptyList()
            is LStmt.Copy -> listOf(st.y)
            is LStmt.Load -> listOf(st.y)
            is LStmt.Store -> listOf(st.x, st.y)
            is LStmt.ALoad -> listOf(st.y)
            is LStmt.AStore -> listOf(st.x, st.y)
            is LStmt.Call -> st.args
        }

        fun defs(st: LStmt): List<Int> = when (st) {
            is LStmt.New -> listOf(st.x)
            is LStmt.Null -> listOf(st.x)
            is LStmt.Copy -> listOf(st.x)
            is LStmt.Load -> listOf(st.x)
            is LStmt.Store -> emptyList()
            is LStmt.ALoad -> listOf(st.x)
            is LStmt.AStore -> emptyList()
            is LStmt.Unknown -> listOf(st.x)
            is LStmt.Call -> listOfNotNull(st.ret)
        }
    }
}

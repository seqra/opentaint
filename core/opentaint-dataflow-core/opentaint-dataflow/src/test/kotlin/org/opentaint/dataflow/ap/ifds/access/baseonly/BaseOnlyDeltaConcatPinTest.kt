package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals

class BaseOnlyDeltaConcatPinTest {
    private val base = AccessPathBase.Argument(0)

    private val s1 = ClassStaticAccessor("S1")
    private val s2 = ClassStaticAccessor("S2")
    private val f1 = FieldAccessor("C", "f1", "T")
    private val f2 = FieldAccessor("C", "f2", "T")
    private val t1 = TaintMarkAccessor("t1")
    private val t2 = TaintMarkAccessor("t2")

    // empty is not a fact (it means "no fact"); every fact carries a terminal (abstract or mark).
    // value(.$) and collapsed(.^) are transient and never persist as domain facts.
    private enum class Suffix { ABSTRACT, MARK1, MARK2 }

    private fun mgr(fieldSensitive: Boolean) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = fieldSensitive)

    private fun BaseOnlyApManager.mkAccess(static: ClassStaticAccessor?, field: FieldAccessor?, suffix: Suffix): BaseOnlyAccess {
        val idxs = ArrayList<Int>(3)
        if (static != null) idxs.add(interner.index(static))
        if (field != null) idxs.add(interner.index(field))
        var isAbstract = false
        when (suffix) {
            Suffix.ABSTRACT -> isAbstract = true
            Suffix.MARK1 -> idxs.add(interner.index(t1))
            Suffix.MARK2 -> idxs.add(interner.index(t2))
        }
        return BaseOnlyAccessOps.build(idxs.toIntArray(), isAbstract)
    }

    // ---- enumerate the representable fact space for a mode ----
    private fun BaseOnlyApManager.facts(): List<BaseOnlyAccess> {
        val statics = listOf(null, s1, s2)
        val fields = if (fieldSensitive) listOf(null, f1, f2) else listOf<FieldAccessor?>(null)
        val suffixes = Suffix.values().toList()
        val out = ArrayList<BaseOnlyAccess>()
        for (st in statics) for (fl in fields) for (sf in suffixes) out.add(mkAccess(st, fl, sf))
        out.add(BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0))
        for (st in statics) {
            val staticIdx = if (st != null) interner.index(st) else NO_ACCESSOR
            out.add(BaseOnlyAccessOps.abstractAt(staticIdx, NO_ACCESSOR, 1))
        }
        return out
    }

    // ---- canonical, mode-independent rendering (stable, no interner-index leakage) ----
    private fun BaseOnlyApManager.label(idx: Int): String = when (idx) {
        interner.index(s1) -> "s1"
        interner.index(s2) -> "s2"
        interner.index(f1) -> "f1"
        interner.index(f2) -> "f2"
        interner.index(t1) -> "t1"
        interner.index(t2) -> "t2"
        else -> "#$idx"
    }

    private fun BaseOnlyApManager.render(a: BaseOnlyAccess, root: String): String {
        val sb = StringBuilder(root)
        when {
            a.staticIdx == ABSTRACT_MARK -> sb.append(".*s")
            a.staticIdx >= 0 -> sb.append(".").append(label(a.staticIdx))
        }
        when {
            a.fieldIdx == ABSTRACT_MARK -> sb.append(".*f")
            a.fieldIdx >= 0 -> sb.append(".").append(label(a.fieldIdx))
        }
        if (a.suffixIdx >= 0) {
            if (a.hasSemanticMark) sb.append(".!").append(label(a.suffixIdx))
            sb.append(".$")
        }
        if (a.isSuffixAbstract) sb.append(".*")
        return sb.toString()
    }

    private fun BaseOnlyApManager.renderFact(a: BaseOnlyAccess): String {
        val body = render(a, "x")
        val tag = when {
            a.isEmpty -> "empty"
            a.hasAp -> "ap@${a.apSlot}"
            a.hasSemanticMark -> "mark"
            a.suffixIdx == FINAL_ACCESSOR_IDX -> "value"
            else -> "open"
        }
        return "%-14s (%2d,%2d,%2d) [%s]".format(body, a.staticIdx, a.fieldIdx, a.suffixIdx, tag)
    }

    private fun BaseOnlyApManager.renderDelta(d: BaseOnlyFinalDelta): String = when (d) {
        BaseOnlyEmptyFinalDelta -> "ε"
        is BaseOnlyNodeFinalDelta -> render(d.access, "Δ")
    }

    private fun dump(m: BaseOnlyApManager): String {
        val sb = StringBuilder()
        val facts = m.facts()

        sb.appendLine("================================================================")
        sb.appendLine("BASE-ONLY delta/concat PIN — mode fieldSensitive=${m.fieldSensitive}")
        sb.appendLine("slots=(static,field,suffix)  suffix: -2=abstract(*) 3=value(\$) >=0-other=mark  (empty is not a fact)")
        sb.appendLine("================================================================")
        sb.appendLine()

        sb.appendLine("## FACTS (${facts.size})")
        facts.forEachIndexed { i, a -> sb.appendLine("  F%02d = %s".format(i, m.renderFact(a))) }
        sb.appendLine()

        // ---- all pairwise deltas: final.delta(initial) ----
        val deltaKeyToId = LinkedHashMap<String, Int>()
        val deltaRender = ArrayList<String>()
        fun deltaId(d: BaseOnlyFinalDelta): Int {
            val key = m.renderDelta(d)
            return deltaKeyToId.getOrPut(key) { deltaRender.add(key); deltaRender.size - 1 }
        }
        // deterministic discovery order: iterate finals then initials
        val cell = Array(facts.size) { arrayOfNulls<String>(facts.size) }
        for (fi in facts.indices) {
            val finalAp = BaseOnlyFinalFactAp(m, base, facts[fi], ExclusionSet.Empty)
            for (ii in facts.indices) {
                val initAp = BaseOnlyInitialFactAp(m, base, facts[ii], ExclusionSet.Empty)
                val deltas = finalAp.delta(initAp)
                cell[fi][ii] = if (deltas.isEmpty()) "-" else
                    deltas.joinToString(",") { "D%d".format(deltaId(it as BaseOnlyFinalDelta)) }
            }
        }

        sb.appendLine("## DISTINCT DELTAS (${deltaRender.size})  [from all ${facts.size}x${facts.size} ordered pairs final.delta(initial)]")
        deltaRender.forEachIndexed { i, r -> sb.appendLine("  D%02d = %s".format(i, r)) }
        sb.appendLine("  ('-' in the matrix below = NO-MATCH, empty delta list)")
        sb.appendLine()

        sb.appendLine("## DELTA MATRIX  cell = F_row.delta(F_col)")
        sb.append("        ")
        for (ii in facts.indices) sb.append("| %-7s".format("F%02d".format(ii)))
        sb.appendLine()
        for (fi in facts.indices) {
            sb.append("  F%02d   ".format(fi))
            for (ii in facts.indices) sb.append("| %-7s".format(cell[fi][ii]))
            sb.appendLine()
        }
        sb.appendLine()

        // ---- all concatenations: fact.concat(delta) ----
        sb.appendLine("## CONCAT MATRIX  cell = F_row.concat(D_col)")
        sb.append("        ")
        for (di in deltaRender.indices) sb.append("| %-14s".format("D%02d".format(di)))
        sb.appendLine()
        // reconstruct delta objects by id (need the actual object; rebuild from a representative pair scan)
        val deltaObjById = arrayOfNulls<BaseOnlyFinalDelta>(deltaRender.size)
        for (fi in facts.indices) {
            val finalAp = BaseOnlyFinalFactAp(m, base, facts[fi], ExclusionSet.Empty)
            for (ii in facts.indices) {
                for (d in finalAp.delta(BaseOnlyInitialFactAp(m, base, facts[ii], ExclusionSet.Empty))) {
                    val id = deltaId(d as BaseOnlyFinalDelta)
                    if (deltaObjById[id] == null) deltaObjById[id] = d
                }
            }
        }
        for (fi in facts.indices) {
            val finalAp = BaseOnlyFinalFactAp(m, base, facts[fi], ExclusionSet.Empty)
            sb.append("  F%02d   ".format(fi))
            for (di in deltaRender.indices) {
                val d = deltaObjById[di]!!
                val res = finalAp.concat(FactTypeChecker.Dummy, d) as BaseOnlyFinalFactAp?
                sb.append("| %-14s".format(res?.let { m.render(it.access, "x") } ?: "null"))
            }
            sb.appendLine()
        }
        sb.appendLine()
        return sb.toString()
    }

    private fun pin(mode: Int) {
        val m = mgr(mode >= 1)
        val actual = dump(m)

        // mirror to scratchpad for review
        val scratch = File("/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/597d4672-dd12-411f-bbdb-d64b06ae40cd/scratchpad/pin_mode$mode.txt")
        scratch.parentFile.mkdirs()
        scratch.writeText(actual)

        val golden = javaClass.getResource("/baseonly/delta_concat_pin_mode$mode.golden.txt")
        if (golden == null) {
            println("PIN mode$mode: no golden resource yet — wrote actual to ${scratch.path}")
        } else {
            assertEquals(golden.readText().trimEnd(), actual.trimEnd(), "delta/concat behaviour changed for mode $mode")
        }
    }

    @Test
    fun `pin mode0`() = pin(0)

    @Test
    fun `pin mode1`() = pin(1)
}

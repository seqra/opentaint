package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals

// Pins that split-delta's field handling is aligned with contains: every (final ⊇ initial)
// pair under the symmetric field-[any] `contains` yields a NON-EMPTY splitDelta (never dropped
// to NO-MATCH), and no non-contained pair yields an ε residual. See
// docs/superpowers/specs/2026-07-10-baseonly-split-delta-alignment-design.md
class BaseOnlySplitDeltaAlignmentTest {
    private val base = AccessPathBase.Argument(0)

    private val s1 = ClassStaticAccessor("S1")
    private val s2 = ClassStaticAccessor("S2")
    private val f1 = FieldAccessor("C", "f1", "T")
    private val f2 = FieldAccessor("C", "f2", "T")
    private val t1 = TaintMarkAccessor("t1")
    private val t2 = TaintMarkAccessor("t2")

    private enum class Suffix { ABSTRACT, VALUE, MARK1, MARK2 }

    private fun mgr(fieldSensitive: Boolean) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = fieldSensitive)

    private fun BaseOnlyApManager.mkAccess(staticIdx: Int, fieldIdx: Int, suffix: Suffix): BaseOnlyAccess {
        val idxs = ArrayList<Int>(3)
        if (staticIdx != NO_ACCESSOR) idxs.add(staticIdx)
        if (fieldIdx != NO_ACCESSOR) idxs.add(fieldIdx)
        var isAbstract = false
        when (suffix) {
            Suffix.ABSTRACT -> isAbstract = true
            Suffix.VALUE -> idxs.add(FINAL_ACCESSOR_IDX)
            Suffix.MARK1 -> idxs.add(interner.index(t1))
            Suffix.MARK2 -> idxs.add(interner.index(t2))
        }
        return BaseOnlyAccessOps.build(idxs.toIntArray(), isAbstract)
    }

    private fun BaseOnlyApManager.statics(): List<Int> =
        listOf(NO_ACCESSOR, interner.index(s1), interner.index(s2))

    private fun BaseOnlyApManager.fields(): List<Int> =
        if (fieldSensitive) listOf(NO_ACCESSOR, interner.index(f1), interner.index(f2), ELEMENT_ACCESSOR_IDX)
        else listOf(NO_ACCESSOR)

    private fun BaseOnlyApManager.facts(): List<BaseOnlyAccess> {
        val out = LinkedHashSet<BaseOnlyAccess>()
        for (st in statics()) for (fl in fields()) {
            for (sf in Suffix.values()) out.add(mkAccess(st, fl, sf))
        }
        out.add(BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0))
        for (st in statics()) out.add(BaseOnlyAccessOps.abstractAt(st, NO_ACCESSOR, 1))
        return out.toList()
    }

    private fun BaseOnlyApManager.label(idx: Int): String = when (idx) {
        interner.index(s1) -> "s1"
        interner.index(s2) -> "s2"
        interner.index(f1) -> "f1"
        interner.index(f2) -> "f2"
        interner.index(t1) -> "t1"
        interner.index(t2) -> "t2"
        ELEMENT_ACCESSOR_IDX -> "[el]"
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

    // classify splitDelta(initial, final): "NM" | "ε" | "Δ..." (+ε if both), and whether it has an ε entry.
    private fun BaseOnlyApManager.splitPairs(final: BaseOnlyAccess, initial: BaseOnlyAccess): List<Pair<BaseOnlyAccess, BaseOnlyInitialDelta>> {
        val initAp = BaseOnlyInitialFactAp(this, base, initial, ExclusionSet.Empty)
        val finalAp = BaseOnlyFinalFactAp(this, base, final, ExclusionSet.Empty)
        return initAp.splitDelta(finalAp).map { (matched, delta) ->
            (matched as BaseOnlyInitialFactAp).access to (delta as BaseOnlyInitialDelta)
        }
    }

    private fun BaseOnlyApManager.renderSplit(final: BaseOnlyAccess, initial: BaseOnlyAccess): String {
        val pairs = splitPairs(final, initial)
        if (pairs.isEmpty()) return "NM"
        return pairs.joinToString("+") { (mAccess, delta) ->
            val d = when (delta) {
                BaseOnlyEmptyInitialDelta -> "ε"
                is BaseOnlyNodeInitialDelta -> render(delta.access, "Δ")
            }
            if (mAccess == initial) d else "[${render(mAccess, "m")}]$d"
        }
    }

    private fun splitHasEmpty(pairs: List<Pair<BaseOnlyAccess, BaseOnlyInitialDelta>>): Boolean =
        pairs.any { it.second === BaseOnlyEmptyInitialDelta }

    // per-pair alignment symbol
    private fun BaseOnlyApManager.sym(final: BaseOnlyAccess, initial: BaseOnlyAccess): String {
        val c = BaseOnlyFinalFactAp(this, base, final, ExclusionSet.Empty)
            .contains(BaseOnlyInitialFactAp(this, base, initial, ExclusionSet.Empty))
        val pairs = splitPairs(final, initial)
        val any = pairs.isNotEmpty()
        val eps = splitHasEmpty(pairs)
        return when {
            c && eps -> "e"      // contained, ε residual (aligned)
            c && any -> "d"      // contained, structural Δ residual (matched, acceptable)
            c && !any -> "X"     // contained but DROPPED (misalignment / FN risk)
            !c && eps -> "S"     // not contained but ε (over-match)
            !c && any -> ":"     // not contained, structural residual (normal extension)
            else -> "."          // not contained, no match
        }
    }

    private fun dump(m: BaseOnlyApManager): String {
        val sb = StringBuilder()
        val facts = m.facts()
        val labels = facts.map { m.render(it, "x") }

        sb.appendLine("================================================================")
        sb.appendLine("BASE-ONLY split-delta vs contains ALIGNMENT PIN — fieldSensitive=${m.fieldSensitive}")
        sb.appendLine("cell (final=row, initial=col):")
        sb.appendLine("  .  not contained, no match           :  not contained, structural residual")
        sb.appendLine("  e  contained, ε residual (aligned)   d  contained, structural Δ residual (matched)")
        sb.appendLine("  X  contained but DROPPED (misalign)  S  not contained but ε (over-match)")
        sb.appendLine("Alignment invariant: no X, no S.")
        sb.appendLine("================================================================")
        sb.appendLine()

        sb.appendLine("## FACTS (${facts.size})")
        facts.forEachIndexed { i, a ->
            val tag = when {
                a.hasAp -> "ap@${a.apSlot}"
                a.hasSemanticMark -> "mark"
                a.suffixIdx == FINAL_ACCESSOR_IDX -> "value"
                else -> "open"
            }
            sb.appendLine("  F%02d = %-16s (%2d,%2d,%2d) [%s]".format(i, labels[i], a.staticIdx, a.fieldIdx, a.suffixIdx, tag))
        }
        sb.appendLine()

        val grid = Array(facts.size) { fi -> Array(facts.size) { ii -> m.sym(facts[fi], facts[ii]) } }

        sb.appendLine("## ALIGNMENT MATRIX")
        sb.append("          ")
        for (ii in facts.indices) sb.append("%-4s".format("F%02d".format(ii)))
        sb.appendLine()
        for (fi in facts.indices) {
            sb.append("  F%02d     ".format(fi))
            for (ii in facts.indices) sb.append("%-4s".format(grid[fi][ii]))
            sb.appendLine()
        }
        sb.appendLine()

        val counts = LinkedHashMap<String, Int>()
        for (fi in facts.indices) for (ii in facts.indices) counts.merge(grid[fi][ii], 1, Int::plus)
        sb.appendLine("## SUMMARY (symbol counts)")
        for ((k, v) in counts) sb.appendLine("  '$k' : $v")
        sb.appendLine()

        sb.appendLine("## CONTAINMENT PAIRS (contained, off-diagonal) — residual per pair")
        sb.appendLine("   final           initial          | sym | splitDelta(i,f)")
        for (fi in facts.indices) for (ii in facts.indices) {
            if (fi == ii) continue
            val s = grid[fi][ii]
            if (s != "e" && s != "d" && s != "X") continue
            sb.appendLine("  %-15s %-15s |  %s  | %s".format(labels[fi], labels[ii], s, m.renderSplit(facts[fi], facts[ii])))
        }
        sb.appendLine()
        return sb.toString()
    }

    private fun assertAligned(m: BaseOnlyApManager) {
        val facts = m.facts()
        val dropped = ArrayList<String>()
        val overMatch = ArrayList<String>()
        for (fi in facts.indices) for (ii in facts.indices) {
            when (m.sym(facts[fi], facts[ii])) {
                "X" -> dropped.add("${m.render(facts[fi], "x")} ⊇ ${m.render(facts[ii], "x")}")
                "S" -> overMatch.add("${m.render(facts[fi], "x")} !⊇ ${m.render(facts[ii], "x")} but ε")
            }
        }
        assertEquals(emptyList(), dropped, "contained pairs dropped by split-delta (fieldSensitive=${m.fieldSensitive})")
        assertEquals(emptyList(), overMatch, "non-contained pairs producing ε (fieldSensitive=${m.fieldSensitive})")
    }

    private fun pin(mode: Int) {
        val m = mgr(mode >= 1)
        val actual = dump(m)
        val scratch = File("/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/597d4672-dd12-411f-bbdb-d64b06ae40cd/scratchpad/splitdelta_align_mode$mode.txt")
        scratch.parentFile.mkdirs()
        scratch.writeText(actual)
        val golden = javaClass.getResource("/baseonly/splitdelta_align_mode$mode.golden.txt")
        if (golden == null) {
            println("PIN splitdelta-align mode$mode: no golden resource yet — wrote actual to ${scratch.path}")
        } else {
            assertEquals(golden.readText().trimEnd(), actual.trimEnd(), "split-delta alignment behaviour changed for mode $mode")
        }
    }

    @Test
    fun `pin mode0`() = pin(0)

    @Test
    fun `pin mode1`() = pin(1)

    @Test
    fun `split-delta is aligned with contains - mode0`() = assertAligned(mgr(false))

    @Test
    fun `split-delta is aligned with contains - mode1`() = assertAligned(mgr(true))
}

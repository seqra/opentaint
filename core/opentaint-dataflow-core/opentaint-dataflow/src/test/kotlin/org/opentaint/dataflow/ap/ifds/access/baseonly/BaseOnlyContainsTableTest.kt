package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals

class BaseOnlyContainsTableTest {
    private val base = AccessPathBase.Argument(0)
    private val other = AccessPathBase.Argument(1)

    private val s1 = ClassStaticAccessor("S1")
    private val s2 = ClassStaticAccessor("S2")
    private val f1 = FieldAccessor("C", "f1", "T")
    private val f2 = FieldAccessor("C", "f2", "T")
    private val t1 = TaintMarkAccessor("t1")
    private val t2 = TaintMarkAccessor("t2")

    private enum class Suffix { ABSTRACT, VALUE, MARK1, MARK2 }

    private fun mgr(fieldSensitive: Boolean) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, org.opentaint.dataflow.util.Cancellation(), fieldSensitive = fieldSensitive)

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

    private fun BaseOnlyApManager.slot(idx: Int): String = when (idx) {
        NO_ACCESSOR -> "-1"
        ABSTRACT_MARK -> "*"
        FINAL_ACCESSOR_IDX -> "$"
        else -> label(idx)
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

    private fun BaseOnlyApManager.tag(a: BaseOnlyAccess): String = when {
        a.isEmpty -> "empty"
        a.hasAp -> "ap@${a.apSlot}"
        a.hasSemanticMark -> "mark"
        a.suffixIdx == FINAL_ACCESSOR_IDX -> "value"
        else -> "open"
    }

    private fun dump(m: BaseOnlyApManager): String {
        val sb = StringBuilder()
        val facts = m.facts()
        val labels = facts.map { m.render(it, "x") }

        sb.appendLine("================================================================")
        sb.appendLine("BASE-ONLY contains PIN — mode fieldSensitive=${m.fieldSensitive}")
        sb.appendLine("cell = F_row(final).contains(F_col(initial));  T = contained, . = not")
        sb.appendLine("contains(i) = sameBase && containsProjected(access, i.access)   [directional coverage plus the documented missing-structural projection match]")
        sb.appendLine("================================================================")
        sb.appendLine()

        sb.appendLine("## FACTS (${facts.size})")
        facts.forEachIndexed { i, a ->
            sb.appendLine("  F%02d = %-14s (%-4s %-4s %-4s) [%s]".format(i, labels[i], m.slot(a.staticIdx), m.slot(a.fieldIdx), m.slot(a.suffixIdx), m.tag(a)))
        }
        sb.appendLine()

        val contains = Array(facts.size) { fi ->
            val finalAp = BaseOnlyFinalFactAp(m, base, facts[fi], ExclusionSet.Empty)
            BooleanArray(facts.size) { ii ->
                finalAp.contains(BaseOnlyInitialFactAp(m, base, facts[ii], ExclusionSet.Empty))
            }
        }

        sb.appendLine("## CONTAINS MATRIX  cell = F_row.contains(F_col)")
        sb.append("          ")
        for (ii in facts.indices) sb.append("%-4s".format("F%02d".format(ii)))
        sb.appendLine()
        for (fi in facts.indices) {
            sb.append("  F%02d     ".format(fi))
            for (ii in facts.indices) sb.append("%-4s".format(if (contains[fi][ii]) "T" else "."))
            sb.appendLine()
        }
        sb.appendLine()

        sb.appendLine("## PER-FACT BREAKDOWN  (initials each final contains; self omitted)")
        for (fi in facts.indices) {
            val hits = facts.indices.filter { it != fi && contains[fi][it] }
            if (hits.isEmpty()) continue
            sb.appendLine("  %-14s contains: %s".format(labels[fi], hits.joinToString(", ") { labels[it] }))
        }
        sb.appendLine()

        // off-diagonal true cells classified
        sb.appendLine("## OFF-DIAGONAL TRUE CELLS (mechanism)")
        var offDiag = 0
        for (fi in facts.indices) for (ii in facts.indices) {
            if (fi == ii || !contains[fi][ii]) continue
            offDiag++
            val cc = BaseOnlyAccessOps.containsAccess(facts[fi], facts[ii])
            val mech = when {
                !cc -> "identity (non-identity!)"
                facts[fi].hasAp -> "containsAccess(abstract-prefix wildcard)"
                else -> "covers(directional virtual field-[any]; suffix+static exact)"
            }
            sb.appendLine("  %-14s contains %-14s : %s".format(labels[fi], labels[ii], mech))
        }
        if (offDiag == 0) sb.appendLine("  (none — contains is pure identity in this mode)")
        sb.appendLine()

        // cross-base probe: does the first clause leak across bases?
        sb.appendLine("## CROSS-BASE PROBE  x-fact.contains(y-same-access)")
        var leak = 0
        for (fi in facts.indices) {
            val xFinal = BaseOnlyFinalFactAp(m, base, facts[fi], ExclusionSet.Empty)
            val yInit = BaseOnlyInitialFactAp(m, other, facts[fi], ExclusionSet.Empty)
            if (xFinal.contains(yInit)) { leak++; if (leak <= 3) sb.appendLine("  LEAK: x.${labels[fi].removePrefix("x")} .contains(y.same) = true") }
        }
        sb.appendLine("  cross-base identical-access contained count = $leak / ${facts.size}")
        sb.appendLine()
        return sb.toString()
    }

    private fun pin(mode: Int) {
        val m = mgr(mode >= 1)
        val actual = dump(m)
        val scratch = File("/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/597d4672-dd12-411f-bbdb-d64b06ae40cd/scratchpad/contains_mode$mode.txt")
        scratch.parentFile.mkdirs()
        scratch.writeText(actual)
        val golden = javaClass.getResource("/baseonly/contains_pin_mode$mode.golden.txt")
        if (golden == null) {
            println("PIN contains mode$mode: no golden resource yet — wrote actual to ${scratch.path}")
        } else {
            fun String.normalizeLineEnds(): String =
                lineSequence().joinToString("\n") { it.trimEnd() }.trimEnd()
            assertEquals(
                golden.readText().normalizeLineEnds(),
                actual.normalizeLineEnds(),
                "contains behaviour changed for mode $mode",
            )
        }
    }

    @Test
    fun `pin mode0`() = pin(0)

    @Test
    fun `pin mode1`() = pin(1)

    // Proves the enumerated fact space contains every abstraction-point fact the engine
    // can produce: (a) the abstractAt(static, field, slot) universe for all slots, and
    // (b) every initial/final pair emitted by the real abstraction machinery over every
    // concrete fact with all accessors excluded (which forces emission at every point).
    @Test
    fun `enumeration covers all abstraction points`() {
        val m = mgr(true)
        val current = m.facts().toSet()

        val abstractAtUniverse = LinkedHashSet<BaseOnlyAccess>()
        for (st in m.statics()) for (fl in m.fields()) for (slot in 0..2) abstractAtUniverse.add(BaseOnlyAccessOps.abstractAt(st, fl, slot))
        val missingAbstractAt = abstractAtUniverse - current
        assertEquals(emptySet(), missingAbstractAt, "abstractAt abstraction points not enumerated")

        val abstraction = BaseOnlyInitialFactAbstraction(m)
        val excl = listOf(s1, s2, f1, f2, t1, t2)
            .fold<org.opentaint.dataflow.ap.ifds.Accessor, ExclusionSet>(ExclusionSet.Empty) { acc, a -> acc.add(a) }
        val emitted = LinkedHashSet<BaseOnlyAccess>()
        for (st in m.statics()) for (fl in m.fields()) for (sf in Suffix.values()) {
            val concrete = m.mkAccess(st, fl, sf)
            abstraction.registerNewInitialFact(BaseOnlyInitialFactAp(m, base, concrete, excl), FactTypeChecker.Dummy)
            abstraction.addAbstractedInitialFact(BaseOnlyFinalFactAp(m, base, concrete, ExclusionSet.Empty), FactTypeChecker.Dummy)
                .forEach { (i, f) ->
                    emitted.add((i as BaseOnlyInitialFactAp).access)
                    emitted.add((f as BaseOnlyFinalFactAp).access)
                }
        }
        val emittedNotEnumerated = emitted - current
        assertEquals(emptySet(), emittedNotEnumerated, "engine-emitted abstraction facts not enumerated")
    }
}

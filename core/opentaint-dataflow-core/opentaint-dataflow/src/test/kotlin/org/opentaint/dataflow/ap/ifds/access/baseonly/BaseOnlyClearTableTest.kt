package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals

// Pin for BaseOnlyAccessOps.clear (the `clearAccessor` operation, spec:
// docs/superpowers/specs/2026-07-13-baseonly-clearaccessor-spec.md). Over the full enumerated
// fact x accessor universe (both modes) it asserts the implementation equals `expectedClear`,
// the spec's denotational reference: clearAccessor(a) = drop every path that begins with `a`.
// Ordinarily this kills a fact exactly when `a` is its first accessor. The compact value-accessor
// state makes Normal and Value roots distinct, so clear removes exactly one fact.
class BaseOnlyClearTableTest {
    private val base = AccessPathBase.Argument(0)

    private val s1 = ClassStaticAccessor("S1")
    private val s2 = ClassStaticAccessor("S2")
    private val f1 = FieldAccessor("C", "f1", "T")
    private val f2 = FieldAccessor("C", "f2", "T")
    private val t1 = TaintMarkAccessor("t1")
    private val t2 = TaintMarkAccessor("t2")
    private val ty1 = TypeInfoAccessor("pkg.Ty1")

    private enum class Suffix { ABSTRACT, VALUE, MARK1, MARK2, TYPE }

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
            Suffix.TYPE -> idxs.add(interner.index(ty1))
        }
        return BaseOnlyAccessOps.build(idxs.toIntArray(), isAbstract)
    }

    private fun BaseOnlyApManager.statics(): List<Int> =
        listOf(NO_ACCESSOR, interner.index(s1), interner.index(s2))

    private fun BaseOnlyApManager.fields(): List<Int> =
        if (fieldSensitive) listOf(NO_ACCESSOR, ANY_ACCESSOR_IDX, interner.index(f1), interner.index(f2), ELEMENT_ACCESSOR_IDX)
        else listOf(NO_ACCESSOR, ANY_ACCESSOR_IDX)

    private fun BaseOnlyApManager.facts(): List<BaseOnlyAccess> {
        val out = LinkedHashSet<BaseOnlyAccess>()
        for (st in statics()) for (fl in fields()) {
            for (sf in Suffix.values()) out.add(mkAccess(st, fl, sf))
        }
        out.add(BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0))
        for (st in statics()) out.add(BaseOnlyAccessOps.abstractAt(st, NO_ACCESSOR, 1))
        return out.toList()
    }

    private fun BaseOnlyApManager.clearIdxs(): List<Pair<String, Int>> = listOf(
        "s1" to interner.index(s1),
        "s2" to interner.index(s2),
        "f1" to interner.index(f1),
        "f2" to interner.index(f2),
        "[el]" to ELEMENT_ACCESSOR_IDX,
        "ANY" to ANY_ACCESSOR_IDX,
        "\$" to FINAL_ACCESSOR_IDX,
        "!t1" to interner.index(t1),
        "!t2" to interner.index(t2),
        "val" to interner.index(ValueAccessor),
        "tig" to TYPE_INFO_GROUP_ACCESSOR_IDX,
        "ty1" to interner.index(ty1),
    )

    private fun BaseOnlyApManager.label(idx: Int): String = when (idx) {
        interner.index(s1) -> "s1"
        interner.index(s2) -> "s2"
        interner.index(f1) -> "f1"
        interner.index(f2) -> "f2"
        interner.index(t1) -> "t1"
        interner.index(t2) -> "t2"
        interner.index(ValueAccessor) -> "val"
        interner.index(ty1) -> "ty1"
        ELEMENT_ACCESSOR_IDX -> "[el]"
        ANY_ACCESSOR_IDX -> "ANY"
        TYPE_INFO_GROUP_ACCESSOR_IDX -> "tig"
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
            when {
                a.suffixIdx.isTypeInfoAccessor() -> sb.append(".tig.").append(label(a.suffixIdx))
                a.hasSemanticMark -> sb.append(".!").append(label(a.suffixIdx))
            }
            sb.append(".$")
        }
        if (a.isSuffixAbstract) sb.append(".*")
        return sb.toString()
    }

    // Reference clearAccessor, independent of the implementation: clearAccessor(a) removes every
    // ground path that begins with `a`. On a single BaseOnly path that is:
    //   - head absent: the direct path is unaffected unless its own suffix is removed;
    //   - a == first accessor -> null;
    //   - otherwise -> keep.
    // Compact terminals retain their covering state when either one of their two root branches is
    // removed. Clear never strips and promotes a tail; that is readAccessor.
    private fun firstAccessor(a: BaseOnlyAccess): Int? = when {
        a.staticIdx >= 0 -> a.staticIdx
        a.fieldIdx >= 0 -> a.fieldIdx
        a.suffixIdx < 0 -> null
        a.suffixIdx == FINAL_ACCESSOR_IDX -> FINAL_ACCESSOR_IDX
        a.suffixIdx.isTypeInfoAccessor() && a.valueAccessorState == BaseOnlyValueAccessorState.Value ->
            TYPE_INFO_GROUP_ACCESSOR_IDX
        else -> a.suffixIdx
    }

    private fun expectedClear(access: BaseOnlyAccess, idx: Int): BaseOnlyAccess? {
        if (access.staticIdx == NO_ACCESSOR && access.fieldIdx == NO_ACCESSOR && access.hasSemanticMark) {
            return access
        }
        val head = firstAccessor(access) ?: return access
        if (head != idx) return access
        return null
    }

    // cell text: current result, and "|ref" appended only when the reference differs.
    //   ·  = result equals the input fact (unchanged / kept)
    //   ∅  = null (fact dropped)
    //   x… = the rendered surviving access path
    //   trailing * on the whole cell = guarded-reachable (startsWith(accessor)==true)
    private fun BaseOnlyApManager.cellText(fact: BaseOnlyAccess, idx: Int): String {
        val cur = BaseOnlyAccessOps.clear(fact, idx)
        val ref = expectedClear(fact, idx)
        fun show(r: BaseOnlyAccess?): String = when {
            r == null -> "∅"
            r == fact -> "·"
            else -> render(r, "x")
        }
        val curS = show(cur)
        val body = if (cur == ref) curS else "$curS|${show(ref)}"
        return body + if (BaseOnlyAccessOps.startsWith(fact, idx)) "*" else ""
    }

    private fun dump(m: BaseOnlyApManager): String {
        val sb = StringBuilder()
        val facts = m.facts()
        val cols = m.clearIdxs()

        sb.appendLine("================================================================")
        sb.appendLine("BASE-ONLY clearAccessor — full result table — mode fieldSensitive=${m.fieldSensitive}")
        sb.appendLine("cell = clear(fact, accessor).  '·'=kept unchanged   '∅'=null(dropped)   'x…'=surviving path")
        sb.appendLine("       'cur|ref' when current diverges from the Tree/Automata reference")
        sb.appendLine("       trailing '*' = guarded-reachable (startsWith(accessor)==true)")
        sb.appendLine("================================================================")
        sb.appendLine()

        val w = 14
        sb.append("  %-17s".format("fact \\ clear"))
        for ((name, _) in cols) sb.append("%-${w}s".format(name))
        sb.appendLine()
        for (a in facts) {
            sb.append("  %-17s".format(m.render(a, "x")))
            for ((_, idx) in cols) sb.append("%-${w}s".format(m.cellText(a, idx)))
            sb.appendLine()
        }
        sb.appendLine()
        return sb.toString()
    }

    private fun run(mode: Int) {
        val m = mgr(mode >= 1)
        for (a in m.facts()) {
            for ((name, idx) in m.clearIdxs()) {
                assertEquals(
                    expectedClear(a, idx),
                    BaseOnlyAccessOps.clear(a, idx),
                    "clear(${m.render(a, "x")}, $name) must equal the clearAccessor spec",
                )
            }
        }
        val out = dump(m)
        val f = File("/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/5f02fec5-1d3b-4bbb-9f1b-6cc2b877e6a5/scratchpad/clear-investigation/clear_mode$mode.txt")
        f.parentFile.mkdirs()
        f.writeText(out)
    }

    @Test
    fun `clear matches spec mode0`() = run(0)

    @Test
    fun `clear matches spec mode1`() = run(1)
}

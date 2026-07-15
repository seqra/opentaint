package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import java.io.File
import kotlin.test.Test
import kotlin.test.assertEquals

// Enumeration pin for BaseOnlyExclusionOps (spec:
// docs/superpowers/specs/2026-07-13-baseonly-exclusion-storage-design.md, §5.1). Over the full
// subset x apSlot universe (both field-sensitivity modes) it asserts:
//   - fromExclusionSet then toExclusionSet == the denotational normalize reference
//     (this subsumes R-lossless-on-well-formed input, N-drops-exactly-below-i, and canonicalization);
//   - contains(compact, idx) matches the membership reference (with type-info-group fallback);
//   - mergeInPlace of two normalized sets == normalize(A union B) at the same slot.
// It also writes a human-readable table to scratchpad.
class BaseOnlyExclusionTableTest {
    private val s1 = ClassStaticAccessor("S1")
    private val s2 = ClassStaticAccessor("S2")
    private val f1 = FieldAccessor("C", "f1", "T")
    private val el = ElementAccessor
    private val t1 = TaintMarkAccessor("t1")
    private val ty1 = TypeInfoAccessor("pkg.Ty1")
    private val tig = TypeInfoGroupAccessor

    private val universe: List<Accessor> = listOf(s1, s2, f1, el, t1, ty1, tig)

    private fun mgr(fieldSensitive: Boolean) =
        BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = fieldSensitive)

    private fun subsets(): List<List<Accessor>> {
        val out = ArrayList<List<Accessor>>()
        for (mask in 0 until (1 shl universe.size)) {
            out.add(universe.filterIndexed { i, _ -> (mask shr i) and 1 == 1 })
        }
        return out
    }

    private fun setOf(accessors: List<Accessor>): ExclusionSet =
        accessors.fold(ExclusionSet.Empty as ExclusionSet) { acc, a -> acc.add(a) }

    // denotational reference: keep an accessor iff its slot is at or below the abstraction point k.
    private fun normalizeRef(ex: ExclusionSet, k: Int, m: BaseOnlyApManager): ExclusionSet = when (ex) {
        ExclusionSet.Empty -> ExclusionSet.Empty
        ExclusionSet.Universe -> ExclusionSet.Universe
        is ExclusionSet.Concrete -> ex.set.fold(ExclusionSet.Empty as ExclusionSet) { acc, a ->
            if (slotOfIdx(m.interner.index(a)) >= k) acc.add(a) else acc
        }
    }

    private fun render(accessors: List<Accessor>): String =
        if (accessors.isEmpty()) "{}" else accessors.joinToString(",") { it.toSuffix() }

    private fun run(mode: Int) {
        val m = mgr(mode >= 1)
        val interner = m.interner
        val sets = subsets()
        val sb = StringBuilder()
        sb.appendLine("BASE-ONLY exclusion normalization table — fieldSensitive=${m.fieldSensitive}")
        sb.appendLine("cell = normalize(set, apSlot) via fromExclusionSet+toExclusionSet")
        sb.appendLine()
        sb.append("%-34s".format("set \\ apSlot"))
        for (k in 0..2) sb.append("%-24s".format("i=$k"))
        sb.appendLine()

        for (accessors in sets) {
            val ex = setOf(accessors)
            sb.append("%-34s".format(render(accessors)))
            for (k in 0..2) {
                val compact = BaseOnlyExclusionOps.fromExclusionSet(ex, interner, k)
                val back = BaseOnlyExclusionOps.toExclusionSet(compact, interner)
                val ref = normalizeRef(ex, k, m)

                assertEquals(ref, back, "normalize(${render(accessors)}, $k) must equal the reference")

                // contains-equivalence: on the normalized compact set, membership matches the
                // normalized reference, extended by the type-info-group fallback.
                for (a in universe) {
                    val idx = interner.index(a)
                    val expected = ref.contains(a) ||
                        (a is TypeInfoAccessor && ref.contains(TypeInfoGroupAccessor))
                    assertEquals(
                        expected,
                        BaseOnlyExclusionOps.contains(compact, idx),
                        "contains(normalize(${render(accessors)}, $k), ${a.toSuffix()})",
                    )
                }
                sb.append("%-24s".format(back.toString()))
            }
            sb.appendLine()
        }

        // merge-equivalence over a representative cross-product (both concrete subsets and the
        // Empty/Universe endpoints), at every apSlot.
        val mergeInputs: List<ExclusionSet> = sets.map { setOf(it) } + listOf(ExclusionSet.Universe)
        for (k in 0..2) {
            for (a in mergeInputs) {
                for (b in mergeInputs) {
                    val ca = BaseOnlyExclusionOps.fromExclusionSet(a, interner, k)
                    val cb = BaseOnlyExclusionOps.fromExclusionSet(b, interner, k)
                    val merged = BaseOnlyExclusionOps.mergeInPlace(ca, cb)
                    val mergedBack = BaseOnlyExclusionOps.toExclusionSet(merged.value, interner)
                    val ref = normalizeRef(a, k, m).union(normalizeRef(b, k, m))
                    assertEquals(ref, mergedBack, "merge(${a}, ${b}) at i=$k")
                }
            }
        }

        val f = File(
            "/tmp/claude-1002/-drive-testcomp-opentaint-go-rules-opentaint/" +
                "5f02fec5-1d3b-4bbb-9f1b-6cc2b877e6a5/scratchpad/exclusion-investigation/exclusion_mode$mode.txt"
        )
        f.parentFile.mkdirs()
        f.writeText(sb.toString())
    }

    @Test
    fun `exclusion ops match spec mode0`() = run(0)

    @Test
    fun `exclusion ops match spec mode1`() = run(1)
}

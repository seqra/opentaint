package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Characterises the shared [TaintCleanActionEvaluator.removeFinalFact] under an any-accessor position,
 * which is what the Go `$*VAR` sanitizer-clean path expresses as
 * `PositionAccess.Complex(base, AnyAccessor)`.
 *
 * Whole-object taint is stored as `base.ANY.mark`; a plain base clean uses `Simple(base)`.
 */
class AnyAccessorCleanTest {
    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = when (accessor) {
            is ElementAccessor -> true
            is FieldAccessor -> true
            is ClassStaticAccessor,
            is AnyAccessor,
            is FinalAccessor,
            is TaintMarkAccessor,
            is TypeInfoAccessor,
            is TypeInfoGroupAccessor -> false
            is ValueAccessor -> error("unexpected accessor to unroll: $accessor")
        }
    }

    private val apManager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val base = AccessPathBase.This
    private val mark = TaintMarkAccessor("m")
    private val field = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("B", "g", "C")

    private val dummyRule = object : CommonTaintConfigurationItem {}
    private val dummyAction = object : CommonTaintAction {}

    private val simple = PositionAccess.Simple(base)
    private val complexAny = PositionAccess.Complex(simple, AnyAccessor)

    private fun fact(vararg accessors: Accessor): FinalFactAp {
        var f = apManager.createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    /** Runs a clean and returns the surviving facts (empty == the mark was fully removed). */
    private fun clean(f: FinalFactAp, from: PositionAccess): List<FinalFactAp> {
        val evaluator = TaintCleanActionEvaluator()
        val evc = EvaluatedCleanAction.initial(FinalFactReader(f, apManager))
        return evaluator.removeFinalFact(evc, from, mark, dummyRule, dummyAction)
            .mapNotNull { it.fact?.factAp }
    }

    @Test
    fun `any-accessor clean removes whole-object taint`() {
        // base.ANY.mark is the single fact that abstractly represents the mark on the base object
        // AND every nested field it exposes. The any-accessor clean removes it entirely.
        val wholeObject = fact(AnyAccessor, mark)
        assertTrue(clean(wholeObject, complexAny).isEmpty(), "any-accessor clean must drop whole-object taint")
    }

    @Test
    fun `any-accessor clean removes a concrete nested-field mark`() {
        // The whole-object ($*C) sanitizer must clear taint stored on a CONCRETE nested field,
        // e.g. base.field.mark, not only the abstract base.ANY.mark. This is the shape a real
        // field-taint fact takes when it reaches a starred sanitizer.
        val nestedField = fact(field, mark)
        assertTrue(
            clean(nestedField, complexAny).isEmpty(),
            "any-accessor clean must remove a concrete nested-field mark",
        )
    }

    @Test
    fun `containsAnyPosition (sink observation) observes a DEPTH-2 concrete field mark`() {
        // The sink `sink($*o)` evaluates ContainsMarkOnAnyField via FactReader.containsAnyPosition
        // (readAnyPosition) — a DIFFERENT path from the clean. This isolates read-boundedness from
        // fact production: construct base.f.g.mark directly and ask if the any-field observation
        // finds the mark under base at depth 2.
        val deep = fact(field, field2, mark) // base.f.g.mark
        val reader = FinalFactReader(deep, apManager)
        val found = reader.containsAnyPosition(PositionAccess.Complex(simple, mark)) // base.<any>.mark
        assertTrue(found != null, "containsAnyPosition must observe a depth-2 concrete field mark; got null")
    }

    @Test
    fun `containsAnyPosition observes a DEPTH-1 concrete field mark`() {
        val d1 = fact(field, mark) // base.f.mark
        val reader = FinalFactReader(d1, apManager)
        assertTrue(
            reader.containsAnyPosition(PositionAccess.Complex(simple, mark)) != null,
            "containsAnyPosition must observe a depth-1 concrete field mark",
        )
    }

    @Test
    fun `any-accessor clean removes a DEPTH-2 concrete nested-field mark`() {
        // KNOWN GAP characterization (StarDeepSink): a concrete mark buried 2 levels deep,
        // base.f.g.mark. If the any-accessor read is truly unbounded-depth, the whole-object
        // clean removes it; if it is depth-1-bounded, the mark survives.
        val deepField = fact(field, field2, mark)
        assertTrue(
            clean(deepField, complexAny).isEmpty(),
            "any-accessor clean must remove a depth-2 concrete nested-field mark (unbounded depth)",
        )
    }

    @Test
    fun `base clean removes the base mark but leaves a nested field mark`() {
        // A simple position cleans the base only.
        val baseMark = fact(mark)
        assertTrue(clean(baseMark, simple).isEmpty(), "base clean must remove the base mark")

        val nestedField = fact(field, mark)
        assertEquals(
            listOf(nestedField),
            clean(nestedField, simple),
            "base clean must NOT reach a concrete nested-field mark",
        )
    }

    @Test
    fun `any-accessor clean on a base-only final fact does not crash`() {
        // A summary fact that is just base.Final (no accessors, no mark) has empty start accessors.
        // An any-accessor clean position (base.ANY.mark.Final) must resolve to "not contained",
        // NOT throw error("Impossible") in the any-accessor read split.
        val bareFinal = fact()
        assertEquals(
            listOf(bareFinal),
            clean(bareFinal, complexAny),
            "any-accessor clean must leave an unrelated base-only final fact untouched",
        )
    }

    @Test
    fun `the two positions are distinct - base clean does not touch whole-object, any clean does not touch a concrete base mark`() {
        // Guards that exact and AnyField positions keep distinct meanings.
        val baseMark = fact(mark)
        assertEquals(
            listOf(baseMark),
            clean(baseMark, complexAny),
            "any-accessor clean targets ANY-stored taint, not a concrete base-only mark",
        )
    }
}

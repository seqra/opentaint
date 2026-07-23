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
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * Characterises the shared [TaintCleanActionEvaluator.removeFinalFact] under an any-accessor position,
 * which is what the Go `$*VAR` sanitizer-clean path asks for via `RemoveMark(onAnyAccessor = true)`
 * (see GoCallRuleBasedSummaryRewriter: `PositionAccess.Complex(base, AnyAccessor)`).
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

    private val apManager = TreeApManager(UnrollStrategy)
    private val base = AccessPathBase.This
    private val mark = TaintMarkAccessor("m")
    private val field = FieldAccessor("A", "f", "B")

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
    fun `base clean removes the base mark but leaves a nested field mark`() {
        // onAnyAccessor = false resolves to Simple(base): it cleans the base position only.
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
    fun `the two positions are distinct - base clean does not touch whole-object, any clean does not touch a concrete base mark`() {
        // Guards that the onAnyAccessor flag actually changes the position handed to removeFinalFact.
        val baseMark = fact(mark)
        assertEquals(
            listOf(baseMark),
            clean(baseMark, complexAny),
            "any-accessor clean targets ANY-stored taint, not a concrete base-only mark",
        )
    }
}

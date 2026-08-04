package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.cactus.CactusApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.TaintCleanReach
import org.opentaint.dataflow.taint.Cleaner
import org.opentaint.dataflow.taint.FinalFactReader
import org.opentaint.dataflow.taint.clean
import org.opentaint.dataflow.taint.PositionAccess
import org.opentaint.dataflow.taint.mkAccessPath
import org.opentaint.dataflow.taint.withSuffix
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class FactCleanerContractTest {
    private val base = AccessPathBase.This
    private val field = FieldAccessor("Box", "value", "String")
    private val nestedField = FieldAccessor("String", "nested", "String")
    private val mark = TaintMarkAccessor("tainted")

    private fun cleaner(vararg accessors: Accessor): Cleaner.Mark =
        Cleaner.Mark(PositionAccess.Simple(base).withSuffix(accessors.toList()), mark, TaintCleanReach.Exact)

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private fun managers(): List<ApManager> = listOf(
        TreeApManager(UnrollStrategy, RefManager(), Cancellation()),
        AutomataApManager(UnrollStrategy, Cancellation()),
        CactusApManager(UnrollStrategy, Cancellation()),
    )

    @Test
    fun `every representation implements the same cleaner boundary`() {
        for (manager in managers()) {
            assertEquals(
                1,
                manager.mostAbstractFinalAp(base)
                    .clean(cleaner(AnyAccessor))
                    .survivingFacts.size,
                "${manager::class.simpleName} must preserve a cleaned abstract fact",
            )

            var concrete = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(field, mark).asReversed()) {
                concrete = concrete.prependAccessor(accessor)
            }

            val cleanResult = concrete.clean(cleaner(AnyAccessor))
            assertTrue(
                cleanResult.survivingFacts.isEmpty() ||
                    cleanResult.survivingFacts.none {
                        it.readAccessor(field)?.startsWithAccessor(mark) == true
                    },
                "${manager::class.simpleName} retained an already-materialized nested mark",
            )
        }
    }

    @Test
    fun `plain and any-field cleaners use the same operation`() {
        for (manager in managers()) {
            var concrete = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(field, mark).asReversed()) {
                concrete = concrete.prependAccessor(accessor)
            }

            val plain = concrete.clean(cleaner(field))
            val anyField = concrete.clean(cleaner(AnyAccessor))

            assertTrue(plain.survivingFacts.isEmpty())
            assertTrue(anyField.survivingFacts.isEmpty())
        }
    }

    @Test
    fun `any-field keeps its meaning below an exact position`() {
        for (manager in managers()) {
            var concrete = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(field, nestedField, mark).asReversed()) {
                concrete = concrete.prependAccessor(accessor)
            }

            val cleaned = concrete.clean(cleaner(field, AnyAccessor))

            assertTrue(
                cleaned.survivingFacts.isEmpty() ||
                    cleaned.survivingFacts.none {
                        it.readAccessor(field)
                            ?.readAccessor(nestedField)
                            ?.startsWithAccessor(mark) == true
                    },
                "${manager::class.simpleName} changed nested AnyField semantics",
            )
        }
    }

    @Test
    fun `every representation finds a mark behind AnyField`() {
        for (manager in managers()) {
            val anyPosition = PositionAccess.Simple(base).withSuffix(listOf(AnyAccessor))
            val fact = manager.mkAccessPath(anyPosition, ExclusionSet.Empty, mark)
            val requiredMark = PositionAccess.Simple(base).withSuffix(listOf(mark))
            assertNotNull(
                FinalFactReader(fact, manager).containsAnyPosition(requiredMark),
                "${manager::class.simpleName} did not find $requiredMark in $fact",
            )
        }
    }

    @Test
    fun `mark cleanup explicitly chooses whether AnyField is a target`() {
        for (manager in managers()) {
            var fact = manager.createFinalAp(base, ExclusionSet.Empty)
            for (accessor in listOf(AnyAccessor, mark).asReversed()) {
                fact = fact.prependAccessor(accessor)
            }
            val exactCleaner = cleaner()
            val anyFieldCleaner = exactCleaner.copy(
                reach = TaintCleanReach.ExactAndAnyField,
            )

            val exactResult = fact.clean(exactCleaner)
            val anyFieldResult = fact.clean(anyFieldCleaner)

            assertEquals(listOf(fact), exactResult.survivingFacts)
            assertTrue(
                anyFieldResult.survivingFacts.isEmpty() ||
                    anyFieldResult.survivingFacts.none {
                        FinalFactReader(it, manager)
                            .containsAnyPosition(PositionAccess.Simple(base).withSuffix(listOf(mark))) != null
                    },
                "${manager::class.simpleName} retained a targeted AnyField mark: " +
                    "$fact -> ${anyFieldResult.survivingFacts}",
            )
        }
    }

}

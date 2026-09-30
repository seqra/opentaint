package org.opentaint.dataflow.ap.ifds.access

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.automata.AutomataApManager
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertEquals

class InitialConcatFinalDeltaTest {
    private val x = AccessPathBase.LocalVar(1)
    private val y = AccessPathBase.LocalVar(2)
    private val a = FieldAccessor("C", "a", "C")
    private val b = FieldAccessor("C", "b", "C")
    private val c = FieldAccessor("C", "c", "C")

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = false
    }

    private fun managers(): List<ApManager> = listOf(
        TreeApManager(UnrollStrategy, RefManager(), Cancellation()),
        AutomataApManager(UnrollStrategy, Cancellation()),
    )

    private fun ApManager.concrete(base: AccessPathBase, vararg path: Accessor): FinalFactAp =
        path.foldRight(createFinalAp(base, ExclusionSet.Empty)) { acc, f -> f.prependAccessor(acc) }

    private fun ApManager.abstractFinal(base: AccessPathBase, vararg path: Accessor): FinalFactAp =
        path.foldRight(mostAbstractFinalAp(base).replaceExclusions(ExclusionSet.Empty)) { acc, f -> f.prependAccessor(acc) }

    private fun ApManager.initial(base: AccessPathBase, vararg path: Accessor): InitialFactAp =
        path.foldRight(mostAbstractInitialAp(base)) { acc, f -> f.prependAccessor(acc) }

    @Test
    fun `node delta is grafted under the initial path`() {
        for (m in managers()) {
            val fact = m.concrete(x, a, b)
            val delta = fact.delta(m.initial(x, a)).single()
            val result = m.initial(y, c).concat(FactTypeChecker.Dummy, delta)
            assertEquals(m.concrete(y, c, b), result, m::class.simpleName)
        }
    }

    @Test
    fun `empty delta yields the abstract initial path`() {
        for (m in managers()) {
            val fact = m.abstractFinal(x, a)
            val delta = fact.delta(m.initial(x, a)).single { it.isEmpty }
            val result = m.initial(y, c).concat(FactTypeChecker.Dummy, delta)
            assertEquals(m.abstractFinal(y, c).toString(), result.toString(), m::class.simpleName)
        }
    }

    @Test
    fun `root initial concat keeps the whole delta`() {
        for (m in managers()) {
            val fact = m.concrete(x, a, b)
            val delta = fact.delta(m.initial(x)).single()
            val result = m.initial(y).concat(FactTypeChecker.Dummy, delta)
            assertEquals(m.concrete(y, a, b).toString(), result.toString(), m::class.simpleName)
        }
    }

    @Test
    fun `initial delta is the suffix after the other path`() {
        for (m in managers()) {
            val fact = m.initial(x, a, b)
            val delta = fact.delta(m.initial(x, a)).single()
            assertEquals(m.initial(y, c, b), m.initial(y, c).concat(delta), m::class.simpleName)
        }
    }

    @Test
    fun `initial delta of an equal path is empty`() {
        for (m in managers()) {
            val delta = m.initial(x, a).delta(m.initial(x, a)).single()
            assertEquals(true, delta.isEmpty, m::class.simpleName)
            assertEquals(m.initial(y), m.initial(y).concat(delta), m::class.simpleName)
        }
    }

    @Test
    fun `initial delta does not match a different path or an excluded suffix`() {
        for (m in managers()) {
            assertEquals(emptyList(), m.initial(x, a, b).delta(m.initial(x, b)), m::class.simpleName)
            assertEquals(emptyList(), m.initial(x, a).delta(m.initial(x, a, b)), m::class.simpleName)
            assertEquals(emptyList(), m.initial(x, a, b).delta(m.initial(x, a).exclude(b)), m::class.simpleName)
            assertEquals(emptyList(), m.initial(x, a).delta(m.initial(y, a)), m::class.simpleName)
        }
    }
}

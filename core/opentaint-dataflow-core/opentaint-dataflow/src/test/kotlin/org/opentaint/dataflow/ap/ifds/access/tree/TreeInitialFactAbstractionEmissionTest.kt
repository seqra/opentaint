package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager
import kotlin.test.Test
import kotlin.test.assertTrue

/**
 * `registerNewInitialFact` restarts the abstraction walk from the base's WHOLE added tree rather
 * than from the fact that changed, so every call re-derives every abstraction the base has ever
 * produced. Only the abstractions the growing exclusion set newly demands are information; the rest
 * are repeats, and the initial edge each one builds is one the method already holds.
 *
 * On a real project that is the dominant shape: the unfold-request answers register a stream of
 * initial facts on the same base, so the walk runs again per answer and re-emits a tree that only
 * ever grows.
 */
class TreeInitialFactAbstractionEmissionTest {
    private companion object {
        const val TYPE_A = "A"
        const val TYPE_B = "B"
        const val TYPE_C = "C"
        const val TYPE_D = "D"

        val FIELD_A_B = FieldAccessor(TYPE_A, "b", TYPE_B)
        val FIELD_B_C = FieldAccessor(TYPE_B, "c", TYPE_C)
        val FIELD_B_E = FieldAccessor(TYPE_B, "e", TYPE_D)
        val FIELD_C_D = FieldAccessor(TYPE_C, "d", TYPE_D)
    }

    private object UnrollStrategy : AnyAccessorUnrollStrategy {
        override fun unrollAccessor(accessor: Accessor): Boolean = accessor is FieldAccessor
    }

    private val apManager = TreeApManager(UnrollStrategy, RefManager(), Cancellation())
    private val abstraction = TreeInitialFactAbstraction(apManager)

    @Test
    fun `a re-registered base re-emits only the abstractions its new exclusion demands`() {
        // The base's added tree carries both `c` and `e` below `b`, so either exclusion has
        // something to split off.
        val seeded = abstraction.addAbstractedInitialFact(
            merge(
                finalFact(AccessPathBase.This, FIELD_A_B, FIELD_B_C, FIELD_C_D),
                finalFact(AccessPathBase.This, FIELD_A_B, FIELD_B_E),
            ),
            FactTypeChecker.Dummy,
        )

        // First answer: `this.b.*` does not cover `c`, so `this.b.c.*` has to exist.
        val first = abstraction.registerNewInitialFact(
            initialFact(AccessPathBase.This, FIELD_A_B).exclude(FIELD_B_C),
            FactTypeChecker.Dummy,
        )

        assertTrue(
            first.any { (initial, _) -> initial == initialFact(AccessPathBase.This, FIELD_A_B, FIELD_B_C) },
            "setup: the first registration should produce this.b.c, produced ${names(first)}",
        )

        // Second answer, same base and same path, one more excluded accessor. The walk restarts from
        // the whole added tree, so it re-derives everything `first` produced as well as `this.b.e`.
        val second = abstraction.registerNewInitialFact(
            initialFact(AccessPathBase.This, FIELD_A_B).exclude(FIELD_B_C).exclude(FIELD_B_E),
            FactTypeChecker.Dummy,
        )

        // Nothing is lost: the accessor the second registration adds is still answered.
        assertTrue(
            second.any { (initial, _) -> initial == initialFact(AccessPathBase.This, FIELD_A_B, FIELD_B_E) },
            "the newly excluded accessor must still produce this.b.e, produced ${names(second)}",
        )

        // And nothing is repeated: an abstraction already handed out is not handed out again.
        val alreadyEmitted = (seeded + first).mapTo(hashSetOf()) { (initial, _) -> initial }
        val repeats = second.filter { (initial, _) -> initial in alreadyEmitted }

        assertTrue(
            repeats.isEmpty(),
            "re-registration re-emitted ${names(repeats)}; already emitted were ${alreadyEmitted.joinToString()}",
        )
    }

    private fun names(facts: List<Pair<InitialFactAp, FinalFactAp>>): String =
        facts.joinToString(prefix = "[", postfix = "]") { (initial, _) -> "$initial" }

    private fun initialFact(base: AccessPathBase, vararg accessors: Accessor): InitialFactAp {
        var fact = apManager.mostAbstractInitialAp(base)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun finalFact(base: AccessPathBase, vararg accessors: Accessor): FinalFactAp {
        var fact = apManager.createFinalAp(base, ExclusionSet.Empty)
        accessors.reversed().forEach { fact = fact.prependAccessor(it) }
        return fact
    }

    private fun merge(fact: FinalFactAp, vararg facts: FinalFactAp): FinalFactAp {
        check(fact is AccessTree)
        return facts.fold(fact) { acc, f ->
            AccessTree(fact.apManager, fact.base, acc.access.mergeAdd((f as AccessTree).access), fact.exclusions)
        }
    }
}

package org.opentaint.dataflow.ap.ifds.access.automata

import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstractionTest
import org.opentaint.dataflow.util.Cancellation

/**
 * The automata backend is out of scope for
 * `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md` (section 3, "Tree backend
 * only"): it still synthesises a concrete accessor out of an `[any]` to match a premise, so it
 * inherits the base class's concrete expectation for
 * [InitialFactAbstractionTest.premiseAccessorUnderAny] where the tree subclass overrides it with
 * the coarse `[any]` that survived R3c/R4's deletion.
 */
class AutomataInitialFactAbstractionTest : InitialFactAbstractionTest() {
    override fun mkApManager(strategy: AnyAccessorUnrollStrategy): ApManager = AutomataApManager(strategy, Cancellation())

    override fun merge(fact: FinalFactAp, vararg facts: FinalFactAp): FinalFactAp {
        check(fact is AccessGraphFinalFactAp)
        return facts.fold(fact) { acc, f ->
            val graph = f as AccessGraphFinalFactAp
            val access = acc.access.merge(graph.access)
            AccessGraphFinalFactAp(fact.base, access, fact.exclusions)
        }
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstractionTest
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.RefManager

class TreeInitialFactAbstractionTest : InitialFactAbstractionTest() {
    /**
     * `literalAnyMatch` is pinned rather than inherited from `-Dopentaint.literalAnyMatch`: the
     * expectations below are the expectations of the literal reader, so the fork must not depend on
     * a global property an ablation run may have flipped.
     */
    override fun mkApManager(strategy: AnyAccessorUnrollStrategy): ApManager =
        TreeApManager(strategy, RefManager(), Cancellation(), literalAnyMatch = true)

    /**
     * ACCEPTED DIVERGENCE, forked rather than deleted so that it stays measured.
     *
     * `docs/superpowers/specs/2026-08-27-literal-any-matching-design.md` deleted
     * `TreeInitialFactAbstraction` R3c -- the rule that emitted a CONCRETE `p.a` for an accessor `a`
     * demanded at this level, covered by an `[any]` and held literally in no branch of the fact --
     * together with R4, the virtual descent that walked back into it. Nothing in the tree backend
     * synthesises a concrete accessor out of an `[any]` in order to match a premise any more, so
     * what R3a already emitted at the same level, `p.[any]`, is now the whole answer.
     *
     * The automata backend is deliberately untouched (design section 3, "Tree backend only") and
     * keeps the base class's concrete premise, so the difference is visible as a difference between
     * the two subclasses rather than as a suppression.
     *
     * This is a widening, not a loss: `p.[any].*` denotes everything `p.a.*` denotes. If it ever
     * goes red -- i.e. the tree emits `p.a` again -- R3c/R4 came back, or `literalAnyMatch` stopped
     * reaching `TreeInitialFactAbstraction`.
     */
    override fun premiseAccessorUnderAny(accessor: Accessor): Accessor = AnyAccessor

    override fun merge(fact: FinalFactAp, vararg facts: FinalFactAp): FinalFactAp {
        check(fact is AccessTree)
        return facts.fold(fact) { acc, f ->
            val tree = f as AccessTree
            val access = acc.access.mergeAdd(tree.access)
            AccessTree(fact.apManager, fact.base, access, fact.exclusions)
        }
    }
}

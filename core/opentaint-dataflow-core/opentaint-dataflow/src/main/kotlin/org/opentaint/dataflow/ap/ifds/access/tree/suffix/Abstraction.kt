package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.typed.TypedInitialFactAbstraction
import org.opentaint.ir.api.common.cfg.CommonInst

class Abstraction(
    val initialStatement: CommonInst,
    val manager: TreeSuffixApManager,
) : TypedInitialFactAbstraction<TreeSuffixInitialFact, TreeSuffixFinalFact> {
    override fun typedAddAbstractedInitialFact(
        factAp: TreeSuffixFinalFact,
        typeChecker: FactTypeChecker
    ): List<Pair<TreeSuffixInitialFact, TreeSuffixFinalFact>> {
        TODO("Not yet implemented")
    }

    override fun typedRegisterNewInitialFact(
        factAp: TreeSuffixInitialFact,
        typeChecker: FactTypeChecker
    ): List<Pair<TreeSuffixInitialFact, TreeSuffixFinalFact>> {
        TODO("Not yet implemented")
    }
}

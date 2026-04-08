package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.ReversedApNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree.AccessNode.Companion.createAbstractNodeFromReversedAp
import org.opentaint.dataflow.ap.ifds.access.tree.TreeInitialFactAbstraction
import org.opentaint.ir.api.common.cfg.CommonInst

class Abstraction(
    val initialStatement: CommonInst,
    override val apManager: TreeSuffixApManager,
) : InitialFactAbstraction,
    TreeSuffixInitialFactAccess, TreeSuffixFinalFactAccess {
    val treeAbstraction = TreeInitialFactAbstraction(apManager.treeManager)

    override fun addAbstractedInitialFact(
        factAp: FinalFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        val added = mutableListOf<Pair<AccessPath.AccessNode?, ReversedApNode?>>()

        val treeNode = getFinalAccess(factAp).toSingleTreeNode()
        treeAbstraction.addAbstractedInitialFact(added, factAp.base, treeNode, typeChecker)

        return added.map { (_, apNode) ->
            val suffix = apManager.treeManager.createAbstractNodeFromReversedAp(apNode)
            val initial = TreeSuffixInitialFact(apManager, factAp.base, access = null, suffix, ExclusionSet.Empty)
            val final = TreeSuffixFinalFact(apManager, factAp.base, access = null, suffix, ExclusionSet.Empty)
            initial to final
        }
    }

    override fun registerNewInitialFact(
        factAp: InitialFactAp,
        typeChecker: FactTypeChecker
    ): List<Pair<InitialFactAp, FinalFactAp>> {
        val added = mutableListOf<Pair<AccessPath.AccessNode?, ReversedApNode?>>()

        TODO("Not yet implemented")
    }

}

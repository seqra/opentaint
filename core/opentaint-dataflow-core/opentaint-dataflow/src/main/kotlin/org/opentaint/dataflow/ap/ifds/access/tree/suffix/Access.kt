package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.FinalApAccess
import org.opentaint.dataflow.ap.ifds.access.common.InitialApAccess
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree


data class FactAccess(
    val access: AccessPath.AccessNode?,
    val suffix: AccessTree.AccessNode,
)

interface TreeSuffixInitialFactAccess : InitialApAccess<FactAccess> {
    val apManager: TreeSuffixApManager

    override fun createInitial(base: AccessPathBase, ap: FactAccess, ex: ExclusionSet): InitialFactAp =
        TreeSuffixInitialFact(apManager, base, ap.access, ap.suffix, ex)

    override fun getInitialAccess(factAp: InitialFactAp): FactAccess {
        val fact = factAp as TreeSuffixInitialFact
        return FactAccess(fact.access, fact.suffix)
    }
}

interface TreeSuffixFinalFactAccess : FinalApAccess<FactAccess> {
    val apManager: TreeSuffixApManager

    override fun createFinal(base: AccessPathBase, ap: FactAccess, ex: ExclusionSet): FinalFactAp =
        TreeSuffixFinalFact(apManager, base, ap.access, ap.suffix, ex)

    override fun getFinalAccess(factAp: FinalFactAp): FactAccess {
        val fact = (factAp as TreeSuffixFinalFact)
        return FactAccess(fact.access, fact.suffix)
    }
}

fun FactAccess.toSingleTreeNode(): AccessTree.AccessNode =
    suffix.prepend(access)

fun AccessTree.AccessNode.prepend(
    prefix: AccessPath.AccessNode?
): AccessTree.AccessNode {
    if (prefix == null) return this

    val next = prepend(prefix.next)
    return next.addParent(prefix.accessor)
}

fun suffixOnlyAccess(suffix: AccessTree.AccessNode): FactAccess =
    FactAccess(access = null, suffix)

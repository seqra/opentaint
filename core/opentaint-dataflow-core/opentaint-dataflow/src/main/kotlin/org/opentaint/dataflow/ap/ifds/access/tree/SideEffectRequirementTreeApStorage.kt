package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonSeReqStorage

class SideEffectRequirementTreeApStorage(
    override val apManager: TreeApManager
) : CommonSeReqStorage<AccessPath.AccessNode?, AccessTree.AccessNode>(),
    TreeInitialApAccess, TreeFinalApAccess {
    override fun createStorage(): Storage<AccessPath.AccessNode?, AccessTree.AccessNode> =
        TreeStorage(apManager)

    class TreeStorage(
        val manager: TreeApManager
    ) : Storage<AccessPath.AccessNode?, AccessTree.AccessNode> {
        val nodeStorage = SideEffectRequirementStorage(manager)

        private var modifiedNodes: MutableList<SideEffectRequirementStorage>? = null

        override fun add(
            requirement: AccessPath.AccessNode?,
            exclusionSet: ExclusionSet
        ): Boolean {
            val element = SideEffectRequirementStorage.Element(requirement, exclusionSet)
            val modified = nodeStorage.mergeAdd(element) ?: return false
            val modifiedList = modifiedNodes
                ?: mutableListOf<SideEffectRequirementStorage>().also { modifiedNodes = it }
            modifiedList.add(modified)
            return true
        }

        override fun getAndResetDelta(
            delta: MutableList<Pair<AccessPath.AccessNode?, ExclusionSet>>
        ) {
            val modified = modifiedNodes?.also { modifiedNodes = null } ?: return
            modified.mapNotNullTo(delta) { n -> n.requirement?.let { it.access to it.exclusions } }
        }

        override fun find(
            dst: MutableList<Pair<AccessPath.AccessNode?, ExclusionSet>>,
            pattern: AccessTree.AccessNode?
        ) {
            val elements = if (pattern != null) {
                nodeStorage.findRequirements(pattern)
            } else {
                nodeStorage.allNodes().mapNotNull { it.requirement }
            }
            elements.mapTo(dst) { it.access to it.exclusions }
        }
    }
}

class SideEffectRequirementStorage(
    val apManager: TreeApManager,
) : AccessBasedStorage<SideEffectRequirementStorage>() {
    data class Element(val access: AccessPath.AccessNode?, val exclusions: ExclusionSet)

    var requirement: Element? = null

    override fun createStorage() = SideEffectRequirementStorage(apManager)

    fun mergeAdd(requirement: Element): SideEffectRequirementStorage? =
        getOrCreateNode(requirement.access).mergeAddCurrent(requirement)

    fun findRequirements(access: AccessTree.AccessNode): Sequence<Element> =
        filterContains(access).mapNotNull { it.requirement }

    private fun mergeAddCurrent(requirement: Element): SideEffectRequirementStorage? {
        val current = this.requirement
        if (current == null) {
            this.requirement = requirement
            return this
        }

        val currentExclusion = current.exclusions
        val mergedExclusion = currentExclusion.union(requirement.exclusions)

        if (mergedExclusion === currentExclusion) return null

        val mergedAp = requirement.copy(exclusions = mergedExclusion)
        this.requirement = mergedAp
        return this
    }
}

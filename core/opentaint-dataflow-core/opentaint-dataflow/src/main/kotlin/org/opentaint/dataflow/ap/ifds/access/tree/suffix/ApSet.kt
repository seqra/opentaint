package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSet
import org.opentaint.dataflow.ap.ifds.access.tree.AccessBasedStorage
import org.opentaint.dataflow.ap.ifds.access.tree.MethodEdgesFinalTreeApSet
import org.opentaint.dataflow.ap.ifds.access.tree.MethodEdgesInitialToFinalTreeApSet.EdgeNonUniverseExclusionMergingStorage
import org.opentaint.dataflow.util.collectToListWithPostProcess
import org.opentaint.ir.api.common.cfg.CommonInst

class FinalApSet(
    methodInitialStatement: CommonInst,
    val maxInstIdx: Int,
    val languageManager: LanguageManager,
    override val apManager: TreeSuffixApManager,
) : CommonZ2FSet<FactAccess>(methodInitialStatement), TreeSuffixFinalFactAccess {
    override fun createApStorage(): ApStorage<FactAccess> = FinalApStorage(maxInstIdx, languageManager, apManager)

    private class FinalApStorage(
        maxInstIdx: Int,
        languageManager: LanguageManager,
        manager: TreeSuffixApManager,
    ) : ApStorage<FactAccess> {
        private val treeStorage = MethodEdgesFinalTreeApSet.ZeroInitialFactEdges(
            maxInstIdx, languageManager, manager.treeManager
        )

        override fun addEdge(statement: CommonInst, accessPath: FactAccess): FactAccess? {
            val treeNode = accessPath.toSingleTreeNode()
            val addedNode = treeStorage.addEdge(statement, treeNode)
                ?: return null

            return suffixOnlyAccess(addedNode)
        }

        override fun collectApAtStatement(statement: CommonInst, dst: MutableList<FactAccess>) {
            collectToListWithPostProcess(
                dst,
                { treeStorage.collectApAtStatement(statement, it) },
                { suffixOnlyAccess(it) }
            )
        }
    }
}

class F2FApSet(
    methodInitialStatement: CommonInst,
    val maxInstIdx: Int,
    val languageManager: LanguageManager,
    override val apManager: TreeSuffixApManager,
) : CommonF2FSet<FactAccess, FactAccess>(methodInitialStatement),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {

    override fun createApStorage(): ApStorage<FactAccess, FactAccess> =
        F2FApStorage(apManager, maxInstIdx, languageManager)

    override fun mostAbstractPattern(base: AccessPathBase): FactAccess =
        FactAccess(access = null, apManager.treeManager.abstractNode)

    // todo: alternate between (fa path -> suffix tree) and (suffix path -> fa tree) ?
    private class F2FApStorage(
        manager: TreeSuffixApManager,
        maxInstIdx: Int,
        languageManager: LanguageManager,
    ) : ApStorage<FactAccess, FactAccess> {
        val storage = IAFAS(manager, maxInstIdx, languageManager)

        override fun add(
            statement: CommonInst,
            fact: AccessPairWithExclusion<FactAccess, FactAccess>
        ): AccessPairWithExclusion<FactAccess, FactAccess>? {
            val normalizedAccess = EdgeNormalization.normalizeFacts(fact.initial, fact.final.access)

            val fas = storage.getOrCreateNode(normalizedAccess.initialAccess).fas
            val suffix = fas.getOrCreateNode(normalizedAccess.finalAccess).suffix

            val suffixWithEx = AccessWithExclusion(normalizedAccess.suffix, fact.final.exclusion)

            // todo: here we may have a problems due to the too aggressive exclusion merge
            suffix.add(statement, suffixWithEx)
                ?: return null

            val addedInitial = FactAccess(normalizedAccess.initialAccess, normalizedAccess.suffix)
            val addedFinal = FactAccess(normalizedAccess.finalAccess, normalizedAccess.suffix)
            return AccessPairWithExclusion(addedInitial, AccessWithExclusion(addedFinal, fact.final.exclusion))
        }

        class IAFAS(
            val manager: TreeSuffixApManager,
            private val maxInstIdx: Int,
            private val languageManager: LanguageManager,
        ) : AccessBasedStorage<IAFAS>() {
            val fas = FAS(manager, maxInstIdx, languageManager)

            override fun createStorage(): IAFAS = IAFAS(manager, maxInstIdx, languageManager)
        }

        class FAS(
            val manager: TreeSuffixApManager,
            private val maxInstIdx: Int,
            private val languageManager: LanguageManager,
        ) : AccessBasedStorage<FAS>() {
            val suffix = EdgeNonUniverseExclusionMergingStorage(maxInstIdx, languageManager, manager.treeManager)

            override fun createStorage(): FAS = FAS(manager, maxInstIdx, languageManager)
        }

        override fun filter(
            dst: MutableList<AccessPairWithExclusion<FactAccess, FactAccess>>,
            statement: CommonInst,
            finalPattern: FactAccess
        ) {
            TODO("Not yet implemented")
        }

        override fun filter(
            dst: MutableList<AccessPairWithExclusion<FactAccess, FactAccess>>,
            statement: CommonInst,
            initial: FactAccess,
            finalPattern: FactAccess
        ) {
            TODO("Not yet implemented")
        }
    }
}

class NdF2FApSet(
    methodInitialStatement: CommonInst,
    val maxInstIdx: Int,
    val languageManager: LanguageManager,
    override val apManager: TreeSuffixApManager,
) : CommonNDF2FSet<FactAccess, FactAccess>(methodInitialStatement, languageManager, maxInstIdx),
    TreeSuffixInitialFactAccess,
    TreeSuffixFinalFactAccess {

    override fun createApStorage(): ApStorage<FactAccess, FactAccess> = NdF2FApStorage()

    override fun mostAbstractPattern(base: AccessPathBase): FactAccess {
        TODO("Not yet implemented")
    }

    private class NdF2FApStorage : ApStorage<FactAccess, FactAccess> {
        override fun add(initial: Set<InitialFactAp>, final: FactAccess): FactAccess? {
            TODO("Not yet implemented")
        }

        override fun filter(
            dst: MutableList<Pair<Set<InitialFactAp>, FactAccess>>,
            finalPattern: FactAccess
        ) {
            TODO("Not yet implemented")
        }

        override fun filter(
            dst: MutableList<FactAccess>,
            initial: Set<InitialFactAp>,
            finalPattern: FactAccess
        ) {
            TODO("Not yet implemented")
        }
    }
}

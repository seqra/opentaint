package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonNDF2FSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonZ2FSet
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath
import org.opentaint.dataflow.ap.ifds.access.tree.AccessTree
import org.opentaint.dataflow.ap.ifds.access.tree.MethodEdgesFinalTreeApSet
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

    override fun createApStorage(): ApStorage<FactAccess, FactAccess> = F2FApStorage()

    override fun mostAbstractPattern(base: AccessPathBase): FactAccess {
        TODO("Not yet implemented")
    }

    private class F2FApStorage : ApStorage<FactAccess, FactAccess> {
        override fun add(
            statement: CommonInst,
            initial: FactAccess,
            final: AccessWithExclusion<FactAccess>
        ): AccessWithExclusion<FactAccess>? {
            TODO("Not yet implemented")
        }

        override fun filter(
            dst: MutableList<Pair<FactAccess, AccessWithExclusion<FactAccess>>>,
            statement: CommonInst,
            finalPattern: FactAccess
        ) {
            TODO("Not yet implemented")
        }

        override fun filter(
            dst: MutableList<AccessWithExclusion<FactAccess>>,
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

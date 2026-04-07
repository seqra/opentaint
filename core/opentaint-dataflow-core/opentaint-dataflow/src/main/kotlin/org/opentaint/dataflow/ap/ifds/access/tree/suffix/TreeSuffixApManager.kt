package org.opentaint.dataflow.ap.ifds.access.tree.suffix

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactSideEffectSummariesApStorage
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactList
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodAccessPathSubscription
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesNDInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodNDInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.SoftReferenceManager
import org.opentaint.ir.api.common.cfg.CommonInst

class TreeSuffixApManager(
    override val anyAccessorUnrollStrategy: AnyAccessorUnrollStrategy,
    val refManager: SoftReferenceManager = SoftReferenceManager(),
    override val cancellation: Cancellation = Cancellation(),
) : ApManager {
    val treeManager = TreeApManager(anyAccessorUnrollStrategy, refManager, cancellation)

    override fun initialFactAbstraction(methodInitialStatement: CommonInst) =
        Abstraction(methodInitialStatement, this)

    override fun methodEdgesFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesFinalApSet = FinalApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesInitialToFinalApSet = F2FApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesNDInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager
    ): MethodEdgesNDInitialToFinalApSet = NdF2FApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun accessPathSubscription(): MethodAccessPathSubscription =
        MethodTreeSuffixAccessPathSubscription(this)

    override fun sideEffectRequirementApStorage(): SideEffectRequirementApStorage =
        SeReqSummaries(this)

    override fun methodFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodFinalApSummariesStorage =
        FinalSummaries(methodInitialStatement, this)

    override fun methodInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodInitialToFinalApSummariesStorage =
        F2FSummaries(methodInitialStatement, this)

    override fun methodNDInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodNDInitialToFinalApSummariesStorage =
        NdF2FSummaries(methodInitialStatement, this)

    override fun factSideEffectSummariesApStorage(methodInitialStatement: CommonInst): FactSideEffectSummariesApStorage =
        SeFactSummaries(methodInitialStatement, this)

    override fun finalFactList(): FinalFactList =
        FactList(this)

    override fun mostAbstractInitialAp(base: AccessPathBase): InitialFactAp = TreeSuffixInitialFact(
        this, base, access = null, suffix = treeManager.abstractNode, ExclusionSet.Empty
    )

    override fun mostAbstractFinalAp(base: AccessPathBase): FinalFactAp = TreeSuffixFinalFact(
        this, base, access = null, suffix = treeManager.abstractNode, ExclusionSet.Empty
    )

    override fun createFinalAp(
        base: AccessPathBase,
        exclusions: ExclusionSet
    ): FinalFactAp = TreeSuffixFinalFact(
        this, base, access = null, suffix = treeManager.finalNode, exclusions
    )

    override fun createAbstractAp(
        base: AccessPathBase,
        exclusions: ExclusionSet
    ): FinalFactAp = TreeSuffixFinalFact(
        this, base, access = null, suffix = treeManager.abstractNode, exclusions
    )

    override fun createFinalInitialAp(
        base: AccessPathBase,
        exclusions: ExclusionSet
    ): InitialFactAp = TreeSuffixInitialFact(
        this, base, access = null, suffix = treeManager.finalNode, exclusions
    )

    override fun createSerializer(context: SummarySerializationContext): ApSerializer =
        Serializer(context, this)
}

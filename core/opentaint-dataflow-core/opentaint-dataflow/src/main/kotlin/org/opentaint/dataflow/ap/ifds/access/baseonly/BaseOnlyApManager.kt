package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet.Empty
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactSideEffectSummariesApStorage
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactList
import org.opentaint.dataflow.ap.ifds.access.InitialFactAbstraction
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.MethodAccessPathSubscription
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesNDInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodNDInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.SideEffectRequirementApStorage
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.serialization.ApSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.common.cfg.CommonInst

class BaseOnlyApManager(
    override val anyAccessorUnrollStrategy: AnyAccessorUnrollStrategy,
    override val cancellation: Cancellation,
    val fieldSensitive: Boolean = false,
    val fieldGeneralizationEnabled: Boolean = false,
    val summaryStorageFieldGeneralizationEnabled: Boolean = false,
) : ApManager {
    val interner = AccessorInterner()

    @Volatile
    private var traceResolutionMode = false


    fun enableTraceResolutionMode() {
        traceResolutionMode = true
    }

    fun traceResolutionModeEnabled(): Boolean = traceResolutionMode

    val Accessor.idx: AccessorIdx get() = interner.index(this)

    val AccessorIdx.accessor: Accessor
        get() = interner.accessor(this) ?: error("Accessor not found: $this")

    val finalAccessorAccess: BaseOnlyAccess get() = FINAL_ACCESS

    override fun mostAbstractInitialAp(base: AccessPathBase): InitialFactAp =
        BaseOnlyInitialFactAp(this, base, ABSTRACT_EMPTY_ACCESS, Empty)

    override fun mostAbstractFinalAp(base: AccessPathBase): FinalFactAp =
        BaseOnlyFinalFactAp(this, base, ABSTRACT_EMPTY_ACCESS, Empty)

    override fun createFinalAp(base: AccessPathBase, exclusions: ExclusionSet): FinalFactAp =
        BaseOnlyFinalFactAp(this, base, finalAccessorAccess, exclusions)

    override fun createFinalInitialAp(base: AccessPathBase, exclusions: ExclusionSet): InitialFactAp =
        BaseOnlyInitialFactAp(this, base, finalAccessorAccess, exclusions)

    fun applyExclusions(suffix: BaseOnlyAccess, exclusions: ExclusionSet): BaseOnlyAccess? =
        when (exclusions) {
            ExclusionSet.Universe -> null
            ExclusionSet.Empty -> suffix
            is ExclusionSet.Concrete -> {
                if (suffix.staticIdx == NO_ACCESSOR && suffix.fieldIdx == NO_ACCESSOR && suffix.hasSemanticMark) {

                    suffix
                } else {
                    val head = suffix.firstAccessorOrNull
                    val accessor = head?.let(interner::accessor)
                    if (accessor == null) suffix else suffix.takeUnless { exclusions.contains(accessor) }
                }
            }
        }

    fun renderAccess(access: BaseOnlyAccess): String {
        val sb = StringBuilder()
        access.forEachAccessorIdx { sb.append(idxToText(it)) }
        if (access.isSuffixAbstract) sb.append(".*")
        if (access.isCollapsed) sb.append(".^")
        return sb.toString()
    }

    private fun idxToText(idx: AccessorIdx): String =
        interner.accessor(idx)?.toSuffix() ?: when {
            idx.isAnyIdx() -> ".[any]"
            idx == FINAL_ACCESSOR_IDX -> ".$"
            idx.isStaticAccessor() -> "<static>"
            idx.isStructuralIdx() -> ".f#$idx"
            else -> ".#$idx"
        }

    override fun initialFactAbstraction(methodInitialStatement: CommonInst): InitialFactAbstraction =
        BaseOnlyInitialFactAbstraction(this)

    override fun methodEdgesFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager,
    ): MethodEdgesFinalApSet =
        MethodEdgesFinalBaseOnlyApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager,
    ): MethodEdgesInitialToFinalApSet =
        MethodEdgesInitialToFinalBaseOnlyApSet(methodInitialStatement, maxInstIdx, languageManager, this)

    override fun methodEdgesNDInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager,
    ): MethodEdgesNDInitialToFinalApSet =
        MethodEdgesNDInitialToFinalBaseOnlyApSet(methodInitialStatement, languageManager, maxInstIdx, this)

    override fun accessPathSubscription(): MethodAccessPathSubscription =
        MethodBaseOnlyAccessPathSubscription(this)

    override fun sideEffectRequirementApStorage(): SideEffectRequirementApStorage =
        BaseOnlySideEffectRequirementApStorage()

    override fun methodFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodFinalApSummariesStorage =
        MethodFinalBaseOnlyApSummariesStorage(methodInitialStatement, this)

    override fun methodInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodInitialToFinalApSummariesStorage =
        MethodInitialToFinalBaseOnlyApSummariesStorage(methodInitialStatement, this)

    override fun methodNDInitialToFinalApSummariesStorage(methodInitialStatement: CommonInst): MethodNDInitialToFinalApSummariesStorage =
        MethodNDInitialToFinalBaseOnlyApSummariesStorage(methodInitialStatement, this)

    override fun factSideEffectSummariesApStorage(methodInitialStatement: CommonInst): FactSideEffectSummariesApStorage =
        FactSESummariesBaseOnlyStorage(methodInitialStatement, this)

    override fun finalFactList(): FinalFactList = BaseOnlyFinalFactList(this)

    override fun createSerializer(context: SummarySerializationContext): ApSerializer =
        BaseOnlySerializer(this, context)

}

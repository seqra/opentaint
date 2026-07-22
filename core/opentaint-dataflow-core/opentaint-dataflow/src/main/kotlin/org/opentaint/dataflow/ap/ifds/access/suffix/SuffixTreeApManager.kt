package org.opentaint.dataflow.ap.ifds.access.suffix

import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.access.MethodEdgesInitialToFinalApSet
import org.opentaint.dataflow.ap.ifds.access.MethodInitialToFinalApSummariesStorage
import org.opentaint.dataflow.ap.ifds.access.MethodAccessPathSubscription
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.SoftReferenceManager
import org.opentaint.ir.api.common.cfg.CommonInst

/**
 * Manager for [org.opentaint.dataflow.ap.ifds.access.ApMode.SuffixTree].
 *
 * Tree factories remain the compatibility surface for individual facts and legacy flow functions;
 * the three paired F2F stores below use the suffix-native relation and edge bundles.
 */
class SuffixTreeApManager(
    anyAccessorUnrollStrategy: AnyAccessorUnrollStrategy,
    refManager: SoftReferenceManager = SoftReferenceManager(),
    cancellation: Cancellation = Cancellation(),
) : TreeApManager(anyAccessorUnrollStrategy, refManager, cancellation) {
    override fun methodEdgesInitialToFinalApSet(
        methodInitialStatement: CommonInst,
        maxInstIdx: Int,
        languageManager: LanguageManager,
    ): MethodEdgesInitialToFinalApSet = MethodEdgesInitialToFinalSuffixTreeSet(
        methodInitialStatement,
        maxInstIdx,
        languageManager,
        this,
    )

    override fun methodInitialToFinalApSummariesStorage(
        methodInitialStatement: CommonInst,
    ): MethodInitialToFinalApSummariesStorage =
        MethodInitialToFinalSuffixTreeSummaries(methodInitialStatement, this)

    override fun accessPathSubscription(): MethodAccessPathSubscription =
        MethodSuffixTreeAccessPathSubscription(this)
}

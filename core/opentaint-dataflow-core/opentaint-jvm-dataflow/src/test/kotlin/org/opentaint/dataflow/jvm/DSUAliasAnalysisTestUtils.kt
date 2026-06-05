package org.opentaint.dataflow.jvm

import org.opentaint.dataflow.jvm.ap.ifds.alias.AAInfoManager
import org.opentaint.dataflow.jvm.ap.ifds.alias.DSUAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.alias.MergeType
import org.opentaint.dataflow.jvm.ap.ifds.alias.State
import org.opentaint.dataflow.jvm.ap.ifds.alias.StateBuilder

abstract class DSUAliasAnalysisTestUtils(protected val mergeType: MergeType) {
    protected val manager = AAInfoManager()
    protected val strategy = DSUAliasAnalysis.DsuMergeStrategy(manager)

    internal inline fun buildState(body: StateBuilder.() -> Unit): State =
        fillState(body).build()

    internal inline fun fillState(body: StateBuilder.() -> Unit): StateBuilder {
        val builder = StateBuilder(manager, strategy, mergeType)
        builder.body()
        return builder
    }
}

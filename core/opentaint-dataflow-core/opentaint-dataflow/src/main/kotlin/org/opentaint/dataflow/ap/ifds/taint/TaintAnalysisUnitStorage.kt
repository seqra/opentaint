package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.AnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.MethodSummariesUnitStorage
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.analysis.AnalysisManager
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

class TaintAnalysisUnitStorage(
    apManager: ApManager,
    analysisManager: AnalysisManager,
    manager: AnalysisUnitRunnerManager? = null,
) : MethodSummariesUnitStorage(
    apManager,
    analysisManager,
    { storage -> manager?.let { analysisManager.onNewSummaryStorage(storage, it) } },
) {
    private data class VulnerabilityIdentity(
        val ruleId: String,
        val statement: CommonInst,
    )

    private var vulnerabilityBuckets = ConcurrentHashMap<VulnerabilityIdentity, TaintSinkTracker.TaintVulnerability>()

    override fun resetApManager(apManager: ApManager) {
        super.resetApManager(apManager)
        vulnerabilityBuckets = ConcurrentHashMap<VulnerabilityIdentity, TaintSinkTracker.TaintVulnerability>()
    }

    fun addVulnerability(vulnerability: TaintSinkTracker.TaintVulnerability) {
        val identity = VulnerabilityIdentity(vulnerability.ruleId, vulnerability.statement)
        val bucket = vulnerabilityBuckets.computeIfAbsent(identity) { vulnerability }

        synchronized(bucket) {
            bucket.mergeAdd(vulnerability)
        }
    }

    fun collectVulnerabilities(collector: MutableList<TaintSinkTracker.TaintVulnerability>) {
        vulnerabilityBuckets.values.forEach {
            collector.add(it)
        }
    }
}

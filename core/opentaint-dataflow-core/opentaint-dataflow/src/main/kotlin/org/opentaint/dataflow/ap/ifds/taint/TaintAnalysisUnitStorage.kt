package org.opentaint.dataflow.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodSummariesUnitStorage
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.ir.api.common.cfg.CommonInst
import java.util.concurrent.ConcurrentHashMap

class TaintAnalysisUnitStorage(apManager: ApManager, languageManager: LanguageManager)
    : MethodSummariesUnitStorage(apManager, languageManager)
{
    private data class VulnerabilityIdentity(
        val ruleId: String,
        val statement: CommonInst,
    )

    private var vulnerabilityBuckets = ConcurrentHashMap<VulnerabilityIdentity, TaintSinkTracker.TaintVulnerability>()
    private val forwardActionableRules = ForwardActionableRulesRecorder()

    override fun resetApManager(apManager: ApManager) {
        super.resetApManager(apManager)
        vulnerabilityBuckets = ConcurrentHashMap<VulnerabilityIdentity, TaintSinkTracker.TaintVulnerability>()
        forwardActionableRules.clear()
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

    fun recordForwardActionableRule(
        statement: CommonInst,
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
    ) = forwardActionableRules.record(statement, rule, action)

    fun collectForwardActionableRules(
        collector: MutableMap<CommonInst, MutableMap<CommonTaintConfigurationItem, MutableSet<CommonTaintAction>>>,
    ) = forwardActionableRules.collectInto(collector)
}

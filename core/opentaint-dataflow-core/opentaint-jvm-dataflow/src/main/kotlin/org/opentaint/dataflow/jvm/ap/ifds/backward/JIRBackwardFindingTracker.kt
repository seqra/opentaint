package org.opentaint.dataflow.jvm.ap.ifds.backward

import org.opentaint.dataflow.ap.ifds.MethodEntryPoint
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.ir.api.jvm.cfg.JIRInst
import java.util.concurrent.ConcurrentHashMap

class JIRBackwardFindingTracker {
    data class BackwardSourceFinding(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSource,
        val mark: TaintMarkAccessor,
    )

    data class BackwardUnconditionalSink(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
    )

    data class BackwardDemandSeed(
        val methodEntryPoint: MethodEntryPoint,
        val statement: JIRInst,
        val rule: TaintConfigurationSink,
        val fact: FinalFactAp,
    )

    private val sourceFindings = ConcurrentHashMap.newKeySet<BackwardSourceFinding>()
    private val unconditionalSinks = ConcurrentHashMap.newKeySet<BackwardUnconditionalSink>()
    private val demandSeeds = ConcurrentHashMap.newKeySet<BackwardDemandSeed>()

    fun addSourceFinding(finding: BackwardSourceFinding) {
        sourceFindings.add(finding)
    }

    fun addUnconditionalSink(finding: BackwardUnconditionalSink) {
        unconditionalSinks.add(finding)
    }

    fun addDemandSeed(seed: BackwardDemandSeed) {
        demandSeeds.add(seed)
    }

    fun sourceFindings(): List<BackwardSourceFinding> = sourceFindings.toList()

    fun unconditionalSinks(): List<BackwardUnconditionalSink> = unconditionalSinks.toList()

    fun demandSeeds(): List<BackwardDemandSeed> = demandSeeds.toList()

    fun reset() {
        sourceFindings.clear()
        unconditionalSinks.clear()
        demandSeeds.clear()
    }
}

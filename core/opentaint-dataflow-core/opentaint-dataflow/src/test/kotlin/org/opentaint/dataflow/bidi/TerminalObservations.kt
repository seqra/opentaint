package org.opentaint.dataflow.bidi

import org.opentaint.dataflow.bidi.ap.Layer
import org.opentaint.dataflow.bidi.fixtures.RunObservation
import org.opentaint.dataflow.bidi.engine.Target

import org.opentaint.dataflow.bidi.driver.Seed
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink

/** Inspect the selected stored observations. An anonymous Target has no sink
 * identity: complete local sink seeds retain its separate observation. */
internal fun RunMethodAnalyzer.observedSink(rule: CommonTaintConfigurationSink, catalog: ReportCatalog): Boolean =
    sinkSeeds.any { it is Seed.Sink && it.rule.id == rule.id } || targets.any {
        val target = it.target as? Target.NormalTarget
        target != null && catalog.descriptor(target.id).key.ruleId == rule.id
    }

internal fun RunResult<RunMethodAnalyzer>.observedSink(rule: CommonTaintConfigurationSink,
                                                     catalog: ReportCatalog): Boolean =
    analyzers.any { it.observedSink(rule, catalog) }

/** Scalar references retain old local witnesses. AP differential checks compare
 * data and protocol geometry only; selected terminal effects have direct tests. */
internal fun RunObservation.dataOnly(): RunObservation =
    copy(witnesses = emptySet(), targets = emptySet(), sinkSeeds = emptySet())

/** Exact local DEMAND seed identities and actual NORMAL terminal identities.
 * No witness tree or per-target anonymous sink identity is reconstructed. */
internal fun RunObservation.observedSinkLayers(): Map<String, Set<Layer>> {
    val result = LinkedHashMap<String, MutableSet<Layer>>()
    for (seed in sinkSeeds) if (seed is Seed.Sink)
        result.getOrPut(seed.rule.id, ::LinkedHashSet).add(Layer.DEMAND)
    for (row in targets) row.sink?.let { key ->
        result.getOrPut(key.ruleId, ::LinkedHashSet).add(Layer.NORMAL)
    }
    return result
}

package org.opentaint.common.sast.sarif

import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.Result
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.ir.api.common.cfg.CommonInst

abstract class DebugFactReachabilitySarifGenerator<IL>(
    val options: SarifGenerationOptions
) {
    abstract val locationResolver: SarifLocationResolver<IL>

    fun generateSarif(
        facts: Map<CommonInst, Set<FinalFactAp>>,
    ): LazyToolRunReport {
        val locations = generateFactLocations(facts)
        val resolvedLocations = locationResolver.resolve(locations)

        val results = resolvedLocations.asSequence().mapIndexedNotNull { index, location ->
            val loc = location.location ?: return@mapIndexedNotNull null
            val ruleId = "s_$index"
            Result(ruleID = ruleId, message = Message(text = loc.message?.text), locations = listOf(loc))
        }

        val run = LazyToolRunReport(
            tool = generateSarifAnalyzerToolDescription(metadatas = emptyList(), options),
            results = results,
        )

        return run
    }

    abstract fun generateFactLocations(statementFacts: Map<CommonInst, Set<FinalFactAp>>): List<IL>
}
package org.opentaint.common.sast.sarif

import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.Result
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.encodeToStream
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.ir.api.common.cfg.CommonInst
import java.io.OutputStream

abstract class DebugFactReachabilitySarifGenerator<IL>(
    val options: SarifGenerationOptions
) {
    abstract val locationResolver: SarifLocationResolver<IL>

    private val json = Json {
        prettyPrint = true
    }

    @OptIn(ExperimentalSerializationApi::class)
    fun generateSarif(
        output: OutputStream,
        facts: Map<CommonInst, Set<FinalFactAp>>,
    ) {
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

        val sarifReport = LazySarifReport.fromRuns(listOf(run))
        json.encodeToStream(sarifReport, output)
    }

    abstract fun generateFactLocations(statementFacts: Map<CommonInst, Set<FinalFactAp>>): List<IL>
}
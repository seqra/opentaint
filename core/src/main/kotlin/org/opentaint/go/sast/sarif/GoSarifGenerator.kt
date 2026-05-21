package org.opentaint.go.sast.sarif

import io.github.detekt.sarif4k.ArtifactLocation
import io.github.detekt.sarif4k.CodeFlow
import io.github.detekt.sarif4k.Level
import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.Result
import io.github.detekt.sarif4k.ThreadFlow
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.encodeToStream
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.inst.GoIRInst
import org.opentaint.jvm.sast.project.SarifGenerationOptions
import org.opentaint.jvm.sast.sarif.InstructionInfo
import org.opentaint.jvm.sast.sarif.IntermediateLocation
import org.opentaint.jvm.sast.sarif.LazySarifReport
import org.opentaint.jvm.sast.sarif.LazyToolRunReport
import org.opentaint.jvm.sast.sarif.LocationType
import org.opentaint.jvm.sast.sarif.TracePathGenerationResult
import org.opentaint.jvm.sast.sarif.TracePathNode
import org.opentaint.jvm.sast.sarif.formatRuleId
import org.opentaint.jvm.sast.sarif.generateSarifAnalyzerToolDescription
import org.opentaint.jvm.sast.sarif.generateTracePath
import java.io.OutputStream
import java.nio.file.Path
import kotlin.io.path.absolutePathString

/**
 * Go counterpart of [org.opentaint.jvm.sast.sarif.SarifGenerator].
 *
 * Converts Go taint vulnerabilities + resolved traces into SARIF, reusing the
 * language-neutral trace-path builder, SARIF data holders, lazy report types and
 * tool-metadata builder. Locations are resolved from [org.opentaint.ir.go.api.GoIRPosition]
 * via [GoLocationResolver]; messages via [GoTraceMessageBuilder].
 */
class GoSarifGenerator(
    private val options: SarifGenerationOptions,
    private val sourceRoot: Path?,
) {
    private val locationResolver = GoLocationResolver(sourceRoot)
    private val json = Json { prettyPrint = true }

    @OptIn(ExperimentalSerializationApi::class)
    fun generateSarif(output: OutputStream, traces: Sequence<VulnerabilityWithTrace>) {
        json.encodeToStream(generateSarif(traces), output)
    }

    fun generateSarif(traces: Sequence<VulnerabilityWithTrace>): LazySarifReport {
        val results = traces.mapNotNull { generateSarifResult(it.vulnerability, it.trace) }

        val uriBase = options.uriBase ?: sourceRoot?.absolutePathString()
        val sourceUri = uriBase?.let {
            mapOf(SarifGenerationOptions.LOCATION_URI to ArtifactLocation(uri = it))
        }

        val run = LazyToolRunReport(
            tool = generateSarifAnalyzerToolDescription(emptyList(), options),
            originalURIBaseIDS = sourceUri,
            results = results,
        )
        return LazySarifReport.fromRuns(listOf(run))
    }

    private fun generateSarifResult(
        vulnerability: TaintSinkTracker.TaintVulnerability,
        trace: TraceResolver.Trace?,
    ): Result? {
        val rule = vulnerability.rule
        val ruleMessage = rule.meta.message
        val level = when (rule.meta.severity) {
            Severity.Note -> Level.Note
            Severity.Warning -> Level.Warning
            Severity.Error -> Level.Error
        }

        val sinkLocation = goStatementLocation(vulnerability.statement)
            ?: run {
                logger.error { "Go vulnerability without GoIRInst sink statement: $vulnerability" }
                return null
            }

        val messageBuilder = GoTraceMessageBuilder(ruleMessage)
        val codeFlows = generateTracePaths(trace).orEmpty().map { path ->
            val flowLocations = path.mapNotNull { node -> flowLocation(node, messageBuilder) }
            CodeFlow(
                threadFlows = listOf(
                    ThreadFlow(locations = locationResolver.toThreadFlowLocations(flowLocations)),
                ),
            )
        }

        return Result(
            ruleID = options.formatRuleId(rule.id),
            message = Message(text = ruleMessage),
            level = level,
            locations = listOf(locationResolver.toSarifLocation(sinkLocation)),
            codeFlows = codeFlows,
        )
    }

    private fun generateTracePaths(trace: TraceResolver.Trace?): List<List<TracePathNode>>? {
        if (trace == null) return null
        return when (val result = generateTracePath(trace)) {
            TracePathGenerationResult.Failure -> {
                logger.warn { "Failed to generate Go trace path for vulnerability trace" }
                null
            }
            TracePathGenerationResult.Simple -> null
            is TracePathGenerationResult.Path -> {
                val limit = options.sarifCodeFlowLimit
                if (limit != null) result.path.take(limit) else result.path
            }
        }
    }

    private fun flowLocation(node: TracePathNode, messageBuilder: GoTraceMessageBuilder): IntermediateLocation? {
        val inst = node.statement as? GoIRInst ?: return null
        // Drop steps with no source position to avoid meaningless SARIF regions.
        if (inst.location.position == null) return null
        return IntermediateLocation(
            inst = inst,
            info = instructionInfo(inst),
            kind = messageBuilder.sarifKind(node),
            message = messageBuilder.messageFor(node),
            type = LocationType.Simple,
        )
    }

    private fun goStatementLocation(statement: CommonInst): IntermediateLocation? {
        val inst = statement as? GoIRInst ?: return null
        return IntermediateLocation(
            inst = inst,
            info = instructionInfo(inst),
            kind = "taint",
            message = null,
            type = LocationType.Simple,
        )
    }

    private fun instructionInfo(inst: GoIRInst): InstructionInfo {
        val function = inst.location.functionBody.function
        val line = inst.location.position?.line ?: -1
        return InstructionInfo(
            fullyQualified = function.fullName,
            machineName = function.name,
            lineNumber = line,
        )
    }

    companion object {
        private val logger = object : KLogging() {}.logger
    }
}

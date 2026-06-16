package org.opentaint.common.sast.sarif

import io.github.detekt.sarif4k.ArtifactLocation
import io.github.detekt.sarif4k.CodeFlow
import io.github.detekt.sarif4k.Level
import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.Result
import io.github.detekt.sarif4k.ThreadFlow
import mu.KLogging
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.TraceResolver
import org.opentaint.dataflow.ap.ifds.trace.VulnerabilityWithTrace
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.semgrep.pattern.RuleMetadata
import java.nio.file.Path
import java.security.MessageDigest
import java.util.Arrays
import kotlin.io.encoding.Base64
import kotlin.io.encoding.ExperimentalEncodingApi
import kotlin.io.path.absolutePathString

abstract class SarifGenerator<IL>(
    val options: SarifGenerationOptions,
    val sourceRoot: Path?
) {
    abstract val locationResolver: SarifLocationResolver<IL>

    data class TraceGenerationStats(
        var total: Int = 0,
        var simple: Int = 0,
        var generatedSuccess: Int = 0,
        var generationFailed: Int = 0,
    )

    val traceGenerationStats = TraceGenerationStats()

    fun generateSarif(
        traces: Sequence<VulnerabilityWithTrace>,
        metadatas: List<RuleMetadata>
    ): LazyToolRunReport {
        val sarifResults = traces.mapNotNull { generateSarifResult(it.vulnerability, it.trace) }

        val uriBase = options.uriBase ?: sourceRoot?.absolutePathString()
        val sourceUri = uriBase?.let {
            mapOf(SarifGenerationOptions.LOCATION_URI to ArtifactLocation(uri = it))
        }

        val run = LazyToolRunReport(
            tool = generateSarifAnalyzerToolDescription(metadatas, options),
            originalURIBaseIDS = sourceUri,
            results = sarifResults.toList().asSequence(),
        )

        return run
    }

    open fun postProcessSarif(
        sarif: Result,
        vulnerability: TaintSinkTracker.TaintVulnerability,
        trace: TraceResolver.Trace?,
        tracePaths: List<List<TracePathNode>>?
    ): Result = sarif

    private fun generateSarifResult(
        vulnerability: TaintSinkTracker.TaintVulnerability,
        trace: TraceResolver.Trace?
    ): Result? {
        val vulnerabilityRule = vulnerability.rule
        val ruleId = vulnerabilityRule.id
        val ruleMessage = Message(text = vulnerabilityRule.meta.message)
        val level = when (vulnerabilityRule.meta.severity) {
            Severity.Note -> Level.Note
            Severity.Warning -> Level.Warning
            Severity.Error -> Level.Error
        }

        val tracePaths = generateTracePaths(trace)
        val threadFlows = tracePaths?.map { generateThreadFlow(it, vulnerabilityRule.meta.message) }

        val sinkLocation = vulnerabilityLocation(vulnerability, threadFlows)
            ?: run {
                logger.error("Invalid vulnerability location: $vulnerability")
                return null
            }

        var partialFingerPrints: Map<String, String>? = null

        if (options.generateFingerprint) {
            val fullFingerprint = computeFingerprint(ruleId, sinkLocation, FingerprintKind.FULL_TRACE, threadFlows)
            val sourceSinkFingerprint = computeFingerprint(ruleId, sinkLocation, FingerprintKind.SOURCE_SINK, threadFlows)
            partialFingerPrints = mapOf(
                "vulnerabilityWithTraceHash/v1" to fullFingerprint,
                "vulnerabilitySourceSinkHash/v1" to sourceSinkFingerprint,
            )
        }

        val resolvedSinkLocation = locationResolver.generateSarifLocation(sinkLocation)
        val resolvedThreadFlows = threadFlows?.map {
            ThreadFlow(locations = locationResolver.resolve(it))
        }

        val result = Result(
            ruleID = options.formatRuleId(ruleId),
            message = ruleMessage,
            level = level,
            partialFingerprints = partialFingerPrints,
            locations = listOf(resolvedSinkLocation),
            codeFlows = resolvedThreadFlows.orEmpty().map { tf -> CodeFlow(threadFlows = listOf(tf)) }
        )

        return postProcessSarif(result, vulnerability, trace, tracePaths)
    }

    private enum class FingerprintKind {
        FULL_TRACE, SOURCE_SINK
    }

    @OptIn(ExperimentalEncodingApi::class)
    private fun computeFingerprint(
        ruleId: String,
        vulnerabilityLocation: IL,
        kind: FingerprintKind,
        traces: List<List<IL>>?
    ): String {
        val digest = MessageDigest.getInstance("SHA-256")
        digest.update(ruleId.toByteArray())
        digest.addLocationFingerprint(vulnerabilityLocation)

        traces
            ?.map { computeTraceFingerprint(it, kind) }
            ?.sortedWith(Arrays::compare)
            ?.forEach(digest::update)

        val digestData = digest.digest()
        return Base64.encode(digestData)
    }

    private fun computeTraceFingerprint(
        trace: List<IL>,
        kind: FingerprintKind,
    ): ByteArray {
        val digest = MessageDigest.getInstance("SHA-256")

        when (kind) {
            FingerprintKind.SOURCE_SINK -> trace.firstOrNull()?.let { digest.addLocationFingerprint(it) }
            FingerprintKind.FULL_TRACE -> trace.forEach { digest.addLocationFingerprint(it) }
        }

        return digest.digest()
    }

    abstract fun MessageDigest.addLocationFingerprint(loc: IL)

    private fun generateTracePaths(trace: TraceResolver.Trace?): List<List<TracePathNode>>? {
        traceGenerationStats.total++

        if (trace == null) {
            traceGenerationStats.generationFailed++
            return null
        }

        val generatedTracePaths = generateTracePath(trace, options.sarifCodeFlowLimit)
        val paths = when (generatedTracePaths) {
            TracePathGenerationResult.Failure -> {
                traceGenerationStats.generationFailed++
                return null
            }

            TracePathGenerationResult.Simple -> {
                traceGenerationStats.simple++
                return null
            }

            is TracePathGenerationResult.Path -> {
                traceGenerationStats.generatedSuccess++
                generatedTracePaths.path
            }
        }

        var limitedTracePaths = paths
        if (options.sarifCodeFlowLimit != null) {
            limitedTracePaths = paths.take(options.sarifCodeFlowLimit)
        }

        return limitedTracePaths
    }

    abstract fun generateThreadFlow(path: List<TracePathNode>, sinkMessage: String): List<IL>

    abstract fun vulnerabilityLocation(
        vulnerability: TaintSinkTracker.TaintVulnerability,
        threadFlows: List<List<IL>>?
    ): IL?

    companion object {
        val logger = object : KLogging() {}.logger
    }
}

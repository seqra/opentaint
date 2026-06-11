package org.opentaint.common.sast

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.encodeToStream
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.encodeToStream
import mu.KLogging
import org.opentaint.common.sast.sarif.LazySarifReport
import org.opentaint.common.sast.sarif.LazyToolRunReport
import org.opentaint.dataflow.ap.ifds.taint.SkippedExternalMethods
import org.opentaint.project.CommonProject
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.outputStream

open class ProjectAnalysisResults(
    val resultDir: Path,
    val options: CommonAnalysisOptions
) {
    val analysisSarifReport = mutableListOf<Pair<CommonProject, LazyToolRunReport>>()
    val factReachabilityReport = mutableListOf<Pair<CommonProject, LazyToolRunReport>>()
    val seVerifiedSarifReport = mutableListOf<Pair<CommonProject, LazyToolRunReport>>()
    val externalMethodsWithoutRules = mutableListOf<Pair<CommonProject, SkippedExternalMethods>>()

    @OptIn(ExperimentalSerializationApi::class)
    open fun writeResults() {
        logger.info { "Write analysis results" }

        if (analysisSarifReport.isNotEmpty()) {
            val report = LazySarifReport.fromRuns(analysisSarifReport.map { it.second })
            (resultDir / options.sarifGenerationOptions.sarifFileName).outputStream().use {
                json.encodeToStream(report, it)
            }
        }

        if (factReachabilityReport.isNotEmpty()) {
            val report = LazySarifReport.fromRuns(factReachabilityReport.map { it.second })
            (resultDir / "debug-ifds-fact-reachability.sarif").outputStream().use {
                json.encodeToStream(report, it)
            }
        }

        if (seVerifiedSarifReport.isNotEmpty()) {
            val report = LazySarifReport.fromRuns(seVerifiedSarifReport.map { it.second })
            val reportName = options.sarifGenerationOptions.sarifFileName + ".se-verified.sarif"
            (resultDir / reportName).outputStream().use {
                json.encodeToStream(report, it)
            }
        }

        if (externalMethodsWithoutRules.isNotEmpty()) {
            val droppedPath = resultDir / DROPPED_EXTERNAL_METHODS_FILE_NAME
            val approximatedPath = resultDir / APPROXIMATED_EXTERNAL_METHODS_FILE_NAME

            val withoutRules = externalMethodsWithoutRules.flatMap { it.second.withoutRules }
            val withRules = externalMethodsWithoutRules.flatMap { it.second.withRules }

            droppedPath.outputStream().use { stream ->
                yaml.encodeToStream(withoutRules, stream)
            }

            approximatedPath.outputStream().use { stream ->
                yaml.encodeToStream(withRules, stream)
            }
        }
    }

    companion object {
        private val logger = object : KLogging() {}.logger

        const val DROPPED_EXTERNAL_METHODS_FILE_NAME = "dropped-external-methods.yaml"
        const val APPROXIMATED_EXTERNAL_METHODS_FILE_NAME = "approximated-external-methods.yaml"

        private val yaml = Yaml(
            configuration = YamlConfiguration(encodeDefaults = true)
        )

        private val json = Json {
            prettyPrint = true
        }
    }
}

package org.opentaint.common.sast.test

import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.encodeToStream
import org.opentaint.common.sast.CommonAnalysisOptions
import org.opentaint.common.sast.ProjectAnalysisResults
import org.opentaint.project.CommonProject
import java.nio.file.Path
import kotlin.io.path.div
import kotlin.io.path.outputStream
import kotlin.reflect.KClass

class ProjectAnalysisTestResults(
    resultDir: Path,
    options: CommonAnalysisOptions
) : ProjectAnalysisResults(resultDir, options) {
    val testResults = mutableListOf<Pair<CommonProject, TestResult<*>>>()
    private val serializers = mutableListOf<Pair<KClass<TestSampleInfo>, KSerializer<TestSampleInfo>>>()

    fun <T : TestSampleInfo> registerTestInfo(info: KClass<T>, serializer: KSerializer<T>) {
        @Suppress("UNCHECKED_CAST")
        this.serializers.add((info as KClass<TestSampleInfo>) to (serializer as KSerializer<TestSampleInfo>))
    }

    @OptIn(ExperimentalSerializationApi::class)
    override fun writeResults() {
        super.writeResults()

        val testResult = testResults.map {
            @Suppress("UNCHECKED_CAST")
            it.second as TestResult<TestSampleInfo>
        }.joinResults()

        val json = Json { prettyPrint = true }
        val serializer = TestResult.serializer(TestSampleInfoSerializer(serializers))
        (resultDir / "test-result.json").outputStream().use { out ->
            json.encodeToStream(serializer, testResult, out)
        }
    }
}

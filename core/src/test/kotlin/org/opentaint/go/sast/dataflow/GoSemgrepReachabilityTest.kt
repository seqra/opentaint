package org.opentaint.go.sast.dataflow

import org.junit.jupiter.api.AfterAll
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.DummySerializationContext
import org.opentaint.dataflow.ap.ifds.EmptyMethodContext
import org.opentaint.dataflow.ap.ifds.MethodWithContext
import org.opentaint.dataflow.ap.ifds.TaintAnalysisUnitRunnerManager
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.tree.TreeApManager
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedItem
import org.opentaint.dataflow.go.GoFunctionSignature
import org.opentaint.dataflow.go.analysis.GoAnalysisManager
import org.opentaint.dataflow.go.graph.GoApplicationGraph
import org.opentaint.dataflow.go.rules.GoTaintConfiguration
import org.opentaint.dataflow.ifds.SingletonUnit
import org.opentaint.dataflow.ifds.UnitResolver
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.common.cfg.CommonInst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.client.GoIRClient
import org.opentaint.ir.go.client.GoIRLoadConfig
import org.opentaint.ir.go.ext.findFunctionByFullName
import org.opentaint.ir.go.type.GoIRUnsafePointerType
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.GoLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.loadGoTaintConfiguration
import org.opentaint.util.analysis.ApplicationGraph
import java.nio.file.Path
import kotlin.io.path.Path
import kotlin.io.path.createTempDirectory
import kotlin.io.path.writeText
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class GoSemgrepReachabilityTest {
    private lateinit var sourcesDir: Path
    private lateinit var client: GoIRClient
    private lateinit var cp: GoIRProgram

    @BeforeAll
    fun setup() {
        sourcesDir = createTempDirectory("go-util-sample")
        for (name in listOf("go.mod", "util.go")) {
            val text = javaClass.classLoader.getResource("go-util-sample/$name")!!.readText()
            sourcesDir.resolve(name).writeText(text)
        }

        client = GoIRClient()
        cp = client.buildFromDir(sourcesDir, GoIRLoadConfig()).program
    }

    @AfterAll
    fun tearDown() {
        if (::client.isInitialized) client.close()
        if (::sourcesDir.isInitialized) sourcesDir.toFile().deleteRecursively()
    }

    @Test
    fun generatedGoRuleReachesSink() {
        // 1. Build the GoTaintConfiguration FROM A SEMGREP RULE (the point of the test).
        val yaml = """
            rules:
              - id: util-source-sink
                languages: [go]
                severity: WARNING
                message: test
                mode: taint
                pattern-sources:
                  - pattern: util.Source(...)
                pattern-sinks:
                  - pattern: util.Sink(${'$'}X)
        """.trimIndent()

        val loader = SemgrepRuleLoader(listOf(GoLanguageStrategy()))
        loader.registerRuleSet(yaml, Path("util-source-sink.yaml"), Path("."), SemgrepLoadTrace())
        val loadedRules = loader.loadRules()
        val rule = loadedRules.rulesWithMeta.first()

        @Suppress("UNCHECKED_CAST")
        val firstRule = rule.first as TaintRuleFromSemgrep<GoSerializedItem>
        val config: GoTaintConfiguration = GoTaintConfiguration().loadGoTaintConfiguration(firstRule)

        // Assert the generated config names match the Go IR; a name mismatch must fail loudly here.
        assertTrue(
            config.sourceForFunction("util.Source".signature(0), allRelevant = false).isNotEmpty(),
            "generated sources must name util.Source",
        )
        assertTrue(
            config.sinkForFunction("util.Sink".signature(1)).isNotEmpty(),
            "generated sinks must name util.Sink",
        )

        // 2. Run go-dataflow with the GENERATED config and assert the sink is reachable.
        val vulnerabilities = runAnalysis(config, "util.Run")
        assertTrue(
            vulnerabilities.isNotEmpty(),
            "Sink util.Sink was not reached from source util.Source in util.Run via the generated config",
        )
    }

    private fun runAnalysis(config: GoTaintConfiguration, entryPointFunction: String): List<*> {
        val entryPoint = cp.findFunctionByFullName(entryPointFunction)
            ?: error("Entry point not found: $entryPointFunction")

        val ifdsGraph = GoApplicationGraph(cp, UtilUnitResolver)

        @Suppress("UNCHECKED_CAST")
        val engine = TaintAnalysisUnitRunnerManager(
            GoAnalysisManager(cp, config),
            ifdsGraph as ApplicationGraph<CommonMethod, CommonInst>,
            unitResolver = UtilUnitResolver as UnitResolver<CommonMethod>,
            apManager = TreeApManager(anyAccessorUnrollStrategy = AnyAccessorUnrollStrategy.AnyAccessorDisabled),
            summarySerializationContext = DummySerializationContext,
            taintRulesStatsSamplingPeriod = null,
        )

        val startMethod = MethodWithContext(entryPoint, EmptyMethodContext)
        return engine.use { eng ->
            eng.runAnalysis(listOf(startMethod), timeout = 1.minutes, cancellationTimeout = 10.seconds)
            eng.getVulnerabilities()
        }
    }

    private object UtilUnitResolver : UnitResolver<GoIRFunction> {
        override fun resolve(method: GoIRFunction): UnitType {
            return when (val pkgName = method.pkg?.importPath) {
                "util" -> SingletonUnit
                else -> UnknownUnit
            }
        }
    }

    private val anyType = GoIRUnsafePointerType

    fun String.signature(args: Int): GoFunctionSignature =
        GoFunctionSignature(this, receiverType = null, paramTypes = List(args) { anyType }, resultType = anyType)
}

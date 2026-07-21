package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedItem
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintPassAction
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.jvm.ifds.PackageUnit
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.ext.packageName
import org.opentaint.jvm.sast.project.spring.SpringRuleProvider
import org.opentaint.semgrep.pattern.SemgrepLoadTrace
import org.opentaint.semgrep.pattern.SemgrepRuleLoader
import org.opentaint.semgrep.pattern.TaintRuleFromSemgrep
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.createTaintConfig
import kotlin.io.path.Path
import kotlin.io.path.readText

/** Reduction of Stirling-PDF's GetInfoOnPDF#getPdfInfo XSS regression. */
class StirlingTraceResolutionRegressionTest : AnalysisTest() {
    override val sourceFileExtension: String = "java"
    override val useDefaultUnrollStrategy: Boolean = true
    override val useDefaultConfig: Boolean = true

    override fun customizeRulesProvider(rulesProvider: TaintRulesProvider): TaintRulesProvider =
        SpringRuleProvider(rulesProvider, requireNotNull(context.springWebProjectContext))

    override fun unitResolver(projectLocation: RegisteredLocation): JIRUnitResolver =
        object : JIRUnitResolver {
            override fun resolve(method: JIRMethod) =
                if (method.enclosingClass.declaration.location == projectLocation) {
                    PackageUnit(method.enclosingClass.packageName)
                } else {
                    UnknownUnit
                }

            override fun locationIsUnknown(loc: RegisteredLocation): Boolean = loc != projectLocation
        }

    @Test
    fun `Tree reports Stirling response vulnerability`() {
        assertReachable(config, DISPATCH_CLASS, DISPATCH_METHOD, RULE_ID, "Stirling Tree control", ApMode.Tree)
    }

    @Test
    fun `BaseOnly reports Stirling response vulnerability`() {
        assertReachable(
            config,
            DISPATCH_CLASS,
            DISPATCH_METHOD,
            RULE_ID,
            "Stirling BaseOnly regression",
            ApMode.BaseOnlyField,
        )
    }

    private val config: SerializedTaintConfig by lazy {
        val generated = generatedJoinConfig()
        generated.copy(
            passThrough = generated.passThrough.orEmpty() + listOf(
                copyRule(EXTERNAL_FACTORY_CLASS, "load", PositionBase.Argument(0), PositionBase.Result),
                copyRule(EXTERNAL_FILE_INPUT_CLASS, "getSize", PositionBase.This, PositionBase.Result),
                copyRule(APPLICATION_PROPERTIES_CLASS, "getValue", PositionBase.This, PositionBase.Result),
                SerializedRule.PassThrough(
                    function = functionMatcher(EXTERNAL_NODE_CLASS, "put"),
                    copy = listOf(
                        SerializedTaintPassAction(
                            from = PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(1)),
                            to = jsonFields(PositionBase.This, "value"),
                        ),
                    ),
                ),
                SerializedRule.PassThrough(
                    function = functionMatcher(EXTERNAL_NODE_CLASS, "set"),
                    copy = listOf(
                        SerializedTaintPassAction(
                            from = jsonFields(PositionBase.Argument(1), "value"),
                            to = jsonFields(PositionBase.This, "value"),
                        ),
                    ),
                ),
                SerializedRule.PassThrough(
                    function = functionMatcher(EXTERNAL_WRITER_CLASS, "writeValueAsString"),
                    copy = listOf(
                        SerializedTaintPassAction(
                            from = jsonFields(PositionBase.Argument(0), "value"),
                            to = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                        ),
                    ),
                ),
            ),
        )
    }

    private fun copyRule(owner: String, name: String, from: PositionBase, to: PositionBase) =
        SerializedRule.PassThrough(
            function = functionMatcher(owner, name),
            copy = listOf(
                SerializedTaintPassAction(
                    from = PositionBaseWithModifiers.BaseOnly(from),
                    to = PositionBaseWithModifiers.BaseOnly(to),
                ),
            ),
        )

    private fun jsonFields(base: PositionBase, vararg fields: String) =
        PositionBaseWithModifiers.WithModifiers(
            base,
            fields.map { PositionModifier.Field(EXTERNAL_NODE_CLASS, it, EXTERNAL_NODE_CLASS) },
        )

    private fun generatedJoinConfig(): SerializedTaintConfig =
        SemgrepRuleLoader(listOf(JavaLanguageStrategy())).run {
            val trace = SemgrepLoadTrace()
            val rulesRoot = Path(System.getProperty("user.dir")).parent.resolve("rules/ruleset")
            listOf(SOURCE_RULE_PATH, SINK_RULE_PATH, SECURITY_RULE_PATH).forEach { relativePath ->
                registerRuleSet(
                    ruleSetText = rulesRoot.resolve(relativePath).readText(),
                    ruleRelativePath = Path(relativePath),
                    rulesRoot = rulesRoot,
                    trace = trace,
                )
            }

            @Suppress("UNCHECKED_CAST")
            val rule = loadRules().rulesWithMeta.single { it.first.ruleId == RULE_ID }.first
                as TaintRuleFromSemgrep<SerializedItem>
            rule.createTaintConfig()
        }

    private companion object {
        const val DISPATCH_CLASS = "__spring_dispatcher__"
        const val DISPATCH_METHOD = "__dispatch__"
        const val EXTERNAL_FILE_INPUT_CLASS = "stirling.external.StirlingExternal\$FileInput"
        const val APPLICATION_PROPERTIES_CLASS =
            "test.samples.StirlingTraceResolutionRegressionPolluter\$ApplicationProperties"
        const val EXTERNAL_FACTORY_CLASS = "stirling.external.StirlingExternal\$PdfDocumentFactory"
        const val EXTERNAL_NODE_CLASS = "stirling.external.StirlingExternal\$JsonNode"
        const val EXTERNAL_WRITER_CLASS = "stirling.external.StirlingExternal\$JsonWriter"
        const val SOURCE_RULE_PATH = "java/lib/spring/untrusted-data-source.yaml"
        const val SINK_RULE_PATH = "java/lib/spring/spring-xss-html-response-sinks.yaml"
        const val SECURITY_RULE_PATH = "java/security/xss.yaml"
        const val RULE_ID = "java/security/xss.yaml:xss-in-spring-app"
    }
}

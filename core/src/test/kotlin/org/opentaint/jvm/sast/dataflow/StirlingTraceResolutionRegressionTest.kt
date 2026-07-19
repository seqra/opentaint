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
    fun `generated Stirling Spring join remains reachable through the exact response helper`() {
        assertReachable(config, TEST_CLASS, "getPdfInfo", RULE_ID, "Stirling Tree control", ApMode.Tree)
        assertReachable(
            config,
            TEST_CLASS,
            "getPdfInfo",
            RULE_ID,
            "Stirling BaseOnly trace-resolution regression",
            ApMode.BaseOnlyField,
        )
    }

    private val config: SerializedTaintConfig by lazy {
        val generated = generatedJoinConfig()
        generated.copy(
            methodExitSink = generated.methodExitSink.orEmpty().filter {
                SINK_MARK in it.condition.toString()
            },
            passThrough = generated.passThrough.orEmpty() + SerializedRule.PassThrough(
                function = functionMatcher(RESPONSE_ENTITY_CLASS, "<init>"),
                copy = listOf(
                    SerializedTaintPassAction(
                        from = PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(0)),
                        to = PositionBaseWithModifiers.WithModifiers(
                            PositionBase.This,
                            listOf(
                                PositionModifier.Field(
                                    HTTP_ENTITY_CLASS,
                                    "Body",
                                    "java.lang.Object",
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
    }

    private fun generatedJoinConfig(): SerializedTaintConfig =
        SemgrepRuleLoader(listOf(JavaLanguageStrategy())).run {
            val trace = SemgrepLoadTrace()
            val rulesRoot = Path(System.getProperty("user.dir")).parent.resolve("rules/ruleset")
            registerRuleSet(
                ruleSetText = rulesRoot.resolve(SOURCE_RULE_PATH).readText(),
                ruleRelativePath = Path(SOURCE_RULE_PATH),
                rulesRoot = rulesRoot,
                trace = trace,
            )
            registerRuleSet(
                ruleSetText = rulesRoot.resolve(SINK_RULE_PATH).readText(),
                ruleRelativePath = Path(SINK_RULE_PATH),
                rulesRoot = rulesRoot,
                trace = trace,
            )
            registerRuleSet(
                ruleSetText = rulesRoot.resolve(SECURITY_RULE_PATH).readText(),
                ruleRelativePath = Path(SECURITY_RULE_PATH),
                rulesRoot = rulesRoot,
                trace = trace,
            )

            @Suppress("UNCHECKED_CAST")
            val rule = loadRules().rulesWithMeta.single { it.first.ruleId == RULE_ID }.first
                as TaintRuleFromSemgrep<SerializedItem>
            rule.createTaintConfig()
        }

    private companion object {
        const val TEST_CLASS = "test.samples.StirlingTraceResolutionRegressionSample"
        const val RESPONSE_ENTITY_CLASS = "org.springframework.http.ResponseEntity"
        const val HTTP_ENTITY_CLASS = "org.springframework.http.HttpEntity"
        const val SOURCE_RULE_PATH = "java/lib/spring/untrusted-data-source.yaml"
        const val SINK_RULE_PATH = "java/lib/spring/spring-xss-html-response-sinks.yaml"
        const val SECURITY_RULE_PATH = "java/security/xss.yaml"
        const val RULE_ID = "java/security/xss.yaml:xss-in-spring-app"
        const val SINK_MARK = "$RULE_ID;sink_35;\$<ARTIFICIAL>_4;6"
    }
}

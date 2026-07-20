package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.assertEquals
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.ApMode
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyAccessOps
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyApManager
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyFinalFactAp
import org.opentaint.dataflow.ap.ifds.access.baseonly.BaseOnlyInitialFactAp
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

/** Reduction of Stirling-PDF's GetInfoOnPDF#getPdfInfo trace-resolution miss. */
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
    fun `Tree resolves generated Stirling response trace`() {
        assertReachable(config, DISPATCH_CLASS, "dispatch", RULE_ID, "Stirling Tree control", ApMode.Tree)
    }

    @Test
    fun `BaseOnly resolves generated Stirling response trace`() {
        // The compact dispatcher also admits a Simple trace. First prove that forward analysis
        // produces the vulnerability, then pin the F2F reversal used by the real Stirling trace.
        assertReachable(
            config,
            DISPATCH_CLASS,
            "dispatch",
            RULE_ID,
            "Stirling BaseOnly trace-resolution regression",
            ApMode.BaseOnlyField,
        )
        assertBaseOnlyCanReverseStirlingResponseSummary()
    }

    private val config: SerializedTaintConfig by lazy {
        val generated = generatedJoinConfig()
        generated.copy(
            methodExitSink = generated.methodExitSink.orEmpty().filter {
                SINK_MARK in it.condition.toString()
            }.map {
                it.copy(
                    function = functionMatcher(TEST_CLASS, "getPdfInfo"),
                )
            },
            passThrough = generated.passThrough.orEmpty() + listOf(
                copyRule(EXTERNAL_FACTORY_CLASS, "load", PositionBase.Argument(0), PositionBase.Result),
                copyRule(EXTERNAL_DOCUMENT_CLASS, "getDocumentInformation", PositionBase.This, PositionBase.Result),
                copyRule(EXTERNAL_INFO_CLASS, "getTitle", PositionBase.This, PositionBase.Result),
                copyRuleWithAccess(
                    EXTERNAL_NODE_CLASS,
                    "put",
                    PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(1)),
                    jsonFields(PositionBase.This, "title"),
                ),
                copyRuleWithAccess(
                    EXTERNAL_NODE_CLASS,
                    "set",
                    jsonFields(PositionBase.Argument(1), "title"),
                    jsonFields(PositionBase.This, "metadata", "title"),
                ),
                SerializedRule.PassThrough(
                    function = functionMatcher(EXTERNAL_WRITER_CLASS, "writeValueAsString"),
                    copy = listOf(
                        SerializedTaintPassAction(
                            from = jsonFields(PositionBase.Argument(0), "metadata", "title"),
                            to = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                        ),
                    ),
                ),
                SerializedRule.PassThrough(
                    function = functionMatcher(RESPONSE_ENTITY_CLASS, "<init>"),
                    copy = listOf(
                        SerializedTaintPassAction(
                            from = PositionBaseWithModifiers.BaseOnly(PositionBase.Argument(0)),
                            to = responseBody(PositionBase.This),
                        ),
                    ),
                ),
            ),
        )
    }

    private fun copyRule(
        owner: String,
        name: String,
        from: PositionBase,
        to: PositionBase,
    ) = SerializedRule.PassThrough(
        function = functionMatcher(owner, name),
        copy = listOf(
            SerializedTaintPassAction(
                from = PositionBaseWithModifiers.BaseOnly(from),
                to = PositionBaseWithModifiers.BaseOnly(to),
            ),
        ),
    )

    private fun copyRuleWithAccess(
        owner: String,
        name: String,
        from: PositionBaseWithModifiers,
        to: PositionBaseWithModifiers,
    ) = SerializedRule.PassThrough(
        function = functionMatcher(owner, name),
        copy = listOf(SerializedTaintPassAction(from = from, to = to)),
    )

    private fun jsonFields(base: PositionBase, vararg fields: String) = PositionBaseWithModifiers.WithModifiers(
        base,
        fields.map { PositionModifier.Field(EXTERNAL_NODE_CLASS, it, EXTERNAL_NODE_CLASS) },
    )

    private fun responseBody(base: PositionBase) = PositionBaseWithModifiers.WithModifiers(
        base,
        listOf(PositionModifier.Field(HTTP_ENTITY_CLASS, "Body", "java.lang.Object")),
    )

    /** Exact F2F boundary produced by bytesToWebResponse in both this sample and Stirling-PDF. */
    private fun assertBaseOnlyCanReverseStirlingResponseSummary() {
        val manager = BaseOnlyApManager(
            AnyAccessorUnrollStrategy.AnyAccessorDisabled,
            fieldSensitive = true,
        )
        val body = manager.interner.index(FieldAccessor(HTTP_ENTITY_CLASS, "Body", "java.lang.Object"))
        val sink = TaintMarkAccessor(SINK_MARK)
        val sinkIdx = manager.interner.index(sink)
        val base = AccessPathBase.Argument(0)
        val summaryAccess = BaseOnlyAccessOps.build(intArrayOf(body), isAbstract = true)
        val callerAccess = BaseOnlyAccessOps.build(intArrayOf(sinkIdx), isAbstract = false)
        val summaryFinal = BaseOnlyFinalFactAp(
            manager,
            base,
            summaryAccess,
            ExclusionSet.Concrete(sink),
        )
        val callerFact = BaseOnlyInitialFactAp(manager, base, callerAccess, ExclusionSet.Empty)

        assertEquals(
            1,
            callerFact.splitDelta(summaryFinal).size,
            "the response summary must retain the semantic sink suffix while reversing the helper call",
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
        const val DISPATCH_CLASS = "test.samples.stirling.dispatch.StirlingDispatcher"
        const val EXTERNAL_FACTORY_CLASS = "stirling.external.StirlingExternal\$PdfDocumentFactory"
        const val EXTERNAL_DOCUMENT_CLASS = "stirling.external.StirlingExternal\$PdfDocument"
        const val EXTERNAL_INFO_CLASS = "stirling.external.StirlingExternal\$DocumentInfo"
        const val EXTERNAL_NODE_CLASS = "stirling.external.StirlingExternal\$JsonNode"
        const val EXTERNAL_WRITER_CLASS = "stirling.external.StirlingExternal\$JsonWriter"
        const val RESPONSE_ENTITY_CLASS = "org.springframework.http.ResponseEntity"
        const val HTTP_ENTITY_CLASS = "org.springframework.http.HttpEntity"
        const val SOURCE_RULE_PATH = "java/lib/spring/untrusted-data-source.yaml"
        const val SINK_RULE_PATH = "java/lib/spring/spring-xss-html-response-sinks.yaml"
        const val SECURITY_RULE_PATH = "java/security/xss.yaml"
        const val RULE_ID = "java/security/xss.yaml:xss-in-spring-app"
        const val SINK_MARK = "$RULE_ID;sink_35;\$<ARTIFICIAL>_4;6"
    }
}

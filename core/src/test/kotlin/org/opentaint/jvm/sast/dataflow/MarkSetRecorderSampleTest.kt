package org.opentaint.jvm.sast.dataflow

import org.junit.jupiter.api.TestInstance
import org.opentaint.common.sast.dataflow.MarkSetOutcome
import org.opentaint.common.sast.dataflow.MarkSetScanOptions
import org.opentaint.dataflow.ap.ifds.markset.MarkSetInput
import org.opentaint.dataflow.configuration.jvm.TaintEntryPointSource
import org.opentaint.dataflow.configuration.jvm.TaintMethodExitSink
import org.opentaint.dataflow.configuration.jvm.TaintStaticFieldSource
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedFieldRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedSimpleNameMatcher
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTypeNameMatcher
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature.JIRLambdaMethod
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRThrowInst
import kotlin.test.Test
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

/**
 * Task 5: the prescan records the mark-set program (spec §4) through the JVM engine hooks:
 * call edges (virtual and lambda), rule sites, exit rules at throws (G6), cleaner atoms at
 * zero call edges (G4) and the covered statements.
 */
@TestInstance(TestInstance.Lifecycle.PER_CLASS)
class MarkSetRecorderSampleTest : AnalysisTest() {
    private companion object {
        const val TEST_CLS = "test.samples.MarkSetSample"
        const val TAINT_MARK = "tainted"
        const val CLEAN_MARK = "cleanable"
        const val ENTRY_MARK = "entry"
        const val FIELD_MARK = "field"
        const val SINK_RULE_ID = "markset-sink"
        const val EXIT_RULE_ID = "markset-exit"
    }

    override val sourceFileExtension: String = "java"

    override val markSet: MarkSetScanOptions = MarkSetScanOptions(enabled = true)

    private val config = SerializedTaintConfig(
        entryPoint = listOf(entryPointRule(TEST_CLS, "shared", ENTRY_MARK, 0)),
        source = listOf(sourceRule(TEST_CLS, "source", TAINT_MARK)),
        sink = listOf(sinkRule(TEST_CLS, "sink", SINK_RULE_ID, listOf(Argument(0) to TAINT_MARK))),
        methodExitSink = listOf(methodExitSinkRule(TEST_CLS, "throwing", EXIT_RULE_ID, TAINT_MARK)),
        cleaner = listOf(
            SerializedRule.Cleaner(
                function = functionMatcher(TEST_CLS, "clean"),
                condition = SerializedCondition.ContainsMark(
                    CLEAN_MARK, PositionBaseWithModifiers.BaseOnly(Argument(0))
                ),
                cleans = listOf(
                    SerializedTaintCleanAction(
                        taintKind = CLEAN_MARK,
                        pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                    )
                ),
            )
        ),
        staticFieldSource = listOf(
            SerializedFieldRule.SerializedStaticFieldSource(
                className = SerializedTypeNameMatcher.ClassPattern(
                    `package` = SerializedSimpleNameMatcher.Simple(TEST_CLS.substringBeforeLast('.')),
                    `class` = SerializedSimpleNameMatcher.Simple(TEST_CLS.substringAfterLast('.')),
                ),
                fieldName = SerializedSimpleNameMatcher.Simple("staticField"),
                condition = null,
                taint = listOf(
                    SerializedTaintAssignAction(
                        kind = FIELD_MARK,
                        pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result),
                    )
                ),
            )
        ),
    )

    private val input: MarkSetInput by lazy {
        runAnalysis(config, TEST_CLS, listOf("entryOne", "entryTwo"))
        assertNotNull(lastMarkSetInput, "the mark-set phase did not seal the recorder")
    }

    private val methods: List<JIRMethod> get() = input.methods.map { it as JIRMethod }

    private fun methodId(name: String): Int =
        methods.indexOfFirst { it.name == name && it.enclosingClass.name == TEST_CLS }
            .also { check(it >= 0) { "method $name was not recorded; recorded: $methods" } }

    private fun calleesOf(name: String): List<JIRMethod> =
        input.program.callees[methodId(name)].map { methods[it] }

    @Test
    fun `edges include the virtual call target, the lambda and the lambda body`() {
        val callees = calleesOf("entryOne")
        assertTrue(
            callees.any { it.name == "handle" && it.enclosingClass.name == "$TEST_CLS\$HandlerImpl" },
            "no edge entryOne -> HandlerImpl.handle; callees: $callees"
        )

        val lambda = callees.singleOrNull { it is JIRLambdaMethod && it.name == "run" }
        assertNotNull(lambda, "no edge entryOne -> lambda; callees: $callees")

        val lambdaCallees = input.program.callees[methods.indexOf(lambda)].map { methods[it] }
        assertTrue(
            lambdaCallees.any { it.name.startsWith("lambda\$entryOne") },
            "no edge lambda -> lambda body; callees: $lambdaCallees"
        )
    }

    @Test
    fun `both entry points share the callee and are roots`() {
        assertTrue(calleesOf("entryOne").any { it.name == "shared" }, "no edge entryOne -> shared")
        assertTrue(calleesOf("entryTwo").any { it.name == "shared" }, "no edge entryTwo -> shared")

        val roots = input.program.roots.map { methods[it].name }.toSet()
        assertTrue(roots.containsAll(listOf("entryOne", "entryTwo")), "roots: $roots")
    }

    @Test
    fun `the exit sink is recorded at the throw statement`() {
        val exitSites = input.sites.filter { it.rule is TaintMethodExitSink }
        assertTrue(
            exitSites.any { it.statement is JIRThrowInst },
            "no exit-sink site at a throw; exit sites at: ${exitSites.map { it.statement }}"
        )
    }

    @Test
    fun `the throw statement is covered`() {
        val throwInst = throwStatement()
        assertTrue(throwInst in input.coveredStatements, "throw $throwInst is not a covered statement")
    }

    @Test
    fun `the cleaner atoms include the cleaner's mark`() {
        val markId = input.markNames.indexOf(CLEAN_MARK)
        assertTrue(markId >= 0, "mark $CLEAN_MARK was never interned; marks: ${input.markNames}")
        assertTrue(input.program.cleanerAtoms[markId], "cleaner atoms miss $CLEAN_MARK")
    }

    @Test
    fun `the entry-point source is recorded at the entry statement of a non-entry method`() {
        val entrySites = input.sites.filter { it.rule is TaintEntryPointSource }
        assertTrue(
            entrySites.any { (it.statement as JIRInst).location.method.name == "shared" },
            "no entry-point source site in shared; entry sites at: ${entrySites.map { it.statement }}"
        )
        assertTrue(entrySites.all { it.genMarks == listOf(ENTRY_MARK) })
    }

    @Test
    fun `the static-field source is recorded at the field read`() {
        val fieldSites = input.sites.filter { it.rule is TaintStaticFieldSource }
        assertTrue(fieldSites.isNotEmpty(), "no static-field source site")
        assertTrue(fieldSites.all { (it.statement as JIRInst).location.method.name == "entryOne" })
    }

    @Test
    fun `the selection never holds a static-field source`() {
        input // runs the analysis
        val outcome = assertIs<MarkSetOutcome.Selected>(lastMarkSetOutcome)
        assertTrue(outcome.rules.values.none { rules -> rules.keys.any { it is TaintStaticFieldSource } })
    }

    private fun throwStatement(): JIRInst {
        val throwing = methods.single { it.name == "throwing" }
        return throwing.instList.single { it is JIRThrowInst }
    }
}

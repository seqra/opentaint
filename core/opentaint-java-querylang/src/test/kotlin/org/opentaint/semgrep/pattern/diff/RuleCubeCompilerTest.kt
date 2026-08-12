package org.opentaint.semgrep.pattern.diff

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta.Severity
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.RuleMetadata
import org.opentaint.semgrep.pattern.SemgrepErrorEntry
import org.opentaint.semgrep.pattern.SemgrepFileLoadTrace
import org.opentaint.semgrep.pattern.SemgrepMatchingRule
import org.opentaint.semgrep.pattern.SemgrepRuleLoadTrace
import org.opentaint.semgrep.pattern.SemgrepTaintRule
import org.opentaint.semgrep.pattern.SemgrepTraceEntry.Step
import org.opentaint.semgrep.pattern.conversion.JavaLanguageStrategy
import org.opentaint.semgrep.pattern.conversion.SemgrepRuleAutomataBuilder
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomataWithStateVars
import org.opentaint.semgrep.pattern.conversion.taint.createTaintAutomata
import org.opentaint.semgrep.pattern.conversion.taint.generateTaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.prepareTaintRules
import org.opentaint.semgrep.pattern.diff.load.ParsedNormalRuleSnapshot
import org.opentaint.semgrep.pattern.diff.load.ParsedRuleDescriptor
import org.opentaint.semgrep.pattern.diff.structure.formulaToDnfCubes
import org.opentaint.semgrep.pattern.parseSemgrepYaml
import org.opentaint.semgrep.pattern.parseMatchingRule
import org.opentaint.semgrep.pattern.parseTaintRule
import kotlin.io.path.Path
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class RuleCubeCompilerTest {
    @Test
    fun `standalone compiler reproduces matching cube preparation`() {
        val fileTrace = SemgrepFileLoadTrace("matching.yaml")
        val yamlRule = parseSemgrepYaml(
            """
            rules:
              - id: matching
                severity: NOTE
                message: test
                languages: [java]
                pattern: sink(${'$'}VALUE)
            """.trimIndent(),
            fileTrace,
        )!!.rules.single()
        val parseTrace = SemgrepRuleLoadTrace("matching.yaml#matching", "matching")
            .stepTrace(Step.LOAD_RULESET)
        val rule = parseMatchingRule(yamlRule, parseTrace)!!
        val descriptor = descriptor("matching.yaml#matching", "matching", "matching.yaml")
        val snapshot = ParsedNormalRuleSnapshot(
            descriptor,
            rule,
            primitiveTracking = false,
            overrideTarget = null,
            metadata = metadata(descriptor),
        )
        val strategy = JavaLanguageStrategy()

        val expectedTrace = SemgrepRuleLoadTrace(descriptor.qualifiedRuleId, descriptor.shortRuleId)
        val built = SemgrepRuleAutomataBuilder(strategy).build(rule, expectedTrace)
        val taintAutomata = createTaintAutomata(
            built,
            expectedTrace.stepTrace(Step.BUILD_TAINT_AUTOMATA),
            strategy.typeOps,
        ) as SemgrepMatchingRule
        val expectedCtx = RuleConversionCtx(
            descriptor.qualifiedRuleId,
            null,
            SinkMetaData(),
            expectedTrace.stepTrace(Step.AUTOMATA_TO_TAINT_RULE),
            strategy.typeOps,
        )
        val builtVariant = taintAutomata.rules.single()
        val expected = expectedCtx.generateTaintAutomataEdges(
            TaintRegisterStateAutomataWithStateVars(builtVariant.rule, emptySet(), emptySet()),
            builtVariant.metaVarInfo,
        )

        val cube = ContextualCube(
            descriptor.qualifiedRuleId,
            RulePartKind.MATCHING,
            0,
            formulaToDnfCubes(rule.rules.single(), parseTrace).single(),
            CubeContext.Matching,
        )
        val actual = RuleCubeCompiler(strategy).compile(
            cube,
            snapshot,
            SemgrepRuleLoadTrace(descriptor.qualifiedRuleId, descriptor.shortRuleId),
        ).variants.single()

        assertSameGeneratedAutomata(expected, actual)
    }

    @Test
    fun `standalone compiler reproduces normal taint role preparation`() {
        val (snapshot, parseTrace) = parseSnapshot(
            """
            rules:
              - id: role-context
                severity: NOTE
                message: test
                languages: [java]
                mode: taint
                pattern-sources:
                  - pattern: ${'$'}VALUE = source()
                pattern-sinks:
                  - pattern: sink(${'$'}VALUE)
                pattern-propagators:
                  - pattern: ${'$'}TO = ${'$'}FROM.copy()
                    from: ${'$'}FROM
                    to: ${'$'}TO
                pattern-sanitizers:
                  - pattern: sanitize(${'$'}VALUE)
            """.trimIndent()
        )
        val rule = snapshot.rule as SemgrepTaintRule<Formula>
        val strategy = JavaLanguageStrategy()

        val expectedTrace = SemgrepRuleLoadTrace(snapshot.descriptor.qualifiedRuleId, "role-context")
        val built = SemgrepRuleAutomataBuilder(strategy).build(rule, expectedTrace)
        val taintAutomata = createTaintAutomata(
            built,
            expectedTrace.stepTrace(Step.BUILD_TAINT_AUTOMATA),
            strategy.typeOps,
        ) as SemgrepTaintRule
        val expectedCtx = RuleConversionCtx(
            snapshot.descriptor.qualifiedRuleId,
            modeModifier = null,
            SinkMetaData(),
            expectedTrace.stepTrace(Step.AUTOMATA_TO_TAINT_RULE),
            strategy.typeOps,
        )
        val expected = expectedCtx.prepareTaintRules(taintAutomata).flatMap {
            listOf(expectedCtx.generateTaintAutomataEdges(it.rule, it.metaVarInfo))
        }

        val compiler = RuleCubeCompiler(strategy)
        val actualTrace = SemgrepRuleLoadTrace(snapshot.descriptor.qualifiedRuleId, "role-context")
        val contextualCubes = listOf(
            ContextualCube(
                snapshot.descriptor.qualifiedRuleId,
                RulePartKind.SOURCE,
                0,
                formulaToDnfCubes(rule.sources.single().pattern, parseTrace).single(),
                CubeContext.Source(rule.sources.single()),
            ) to expected.source.single().rule,
            ContextualCube(
                snapshot.descriptor.qualifiedRuleId,
                RulePartKind.SINK,
                0,
                formulaToDnfCubes(rule.sinks.single().pattern, parseTrace).single(),
                CubeContext.Sink(rule.sinks.single()),
            ) to expected.sink.single().rule,
            ContextualCube(
                snapshot.descriptor.qualifiedRuleId,
                RulePartKind.PROPAGATOR,
                0,
                formulaToDnfCubes(rule.propagators.single().pattern, parseTrace).single(),
                CubeContext.Propagator(rule.propagators.single()),
            ) to expected.pass.single().rule,
            ContextualCube(
                snapshot.descriptor.qualifiedRuleId,
                RulePartKind.SANITIZER,
                0,
                formulaToDnfCubes(rule.sanitizers.single().pattern, parseTrace).single(),
                CubeContext.Sanitizer(rule.sanitizers.single()),
            ) to expected.clean.single().rule,
        )

        contextualCubes.forEach { (cube, expectedEdges) ->
            val variants = compiler.compile(cube, snapshot, actualTrace).variants
            assertEquals(1, variants.size, "unexpected variant count for ${cube.declarationKind}")
            assertSameGeneratedAutomata(expectedEdges, variants.single())
        }

        assertTrue(actualTrace.steps.flatMap { it.entries }.none { it is SemgrepErrorEntry })
    }

    private fun parseSnapshot(yaml: String): Pair<ParsedNormalRuleSnapshot, org.opentaint.semgrep.pattern.SemgrepRuleLoadStepTrace> {
        val fileTrace = SemgrepFileLoadTrace("test.yaml")
        val yamlRule = parseSemgrepYaml(yaml, fileTrace)!!.rules.single()
        val parseTrace = SemgrepRuleLoadTrace("test.yaml#role-context", "role-context")
            .stepTrace(Step.LOAD_RULESET)
        val rule = parseTaintRule(yamlRule, parseTrace)
        val descriptor = descriptor("test.yaml#role-context", "role-context", "test.yaml")
        return ParsedNormalRuleSnapshot(
            descriptor,
            rule,
            primitiveTracking = false,
            overrideTarget = null,
            metadata = metadata(descriptor),
        ) to parseTrace
    }

    private fun descriptor(qualifiedId: String, shortId: String, path: String) = ParsedRuleDescriptor(
        qualifiedRuleId = qualifiedId,
        shortRuleId = shortId,
        language = "java",
        relativePath = Path(path),
        isLibraryRule = false,
        isDisabled = false,
    )

    private fun metadata(descriptor: ParsedRuleDescriptor) = RuleMetadata(
        descriptor.qualifiedRuleId,
        descriptor.shortRuleId,
        "test",
        Severity.Note,
        metadata = null,
    )

    /** MethodFormulaManager is intentionally identity-based, so compare its graph projections. */
    private fun assertSameGeneratedAutomata(expected: TaintAutomataEdges, actual: TaintAutomataEdges) {
        assertEquals(expected.automata.initial, actual.automata.initial)
        assertEquals(expected.automata.finalAcceptStates, actual.automata.finalAcceptStates)
        assertEquals(expected.automata.finalDeadStates, actual.automata.finalDeadStates)
        assertEquals(expected.automata.successors, actual.automata.successors)
        assertEquals(expected.metaVarInfo, actual.metaVarInfo)
        assertEquals(expected.globalStateAssignStates, actual.globalStateAssignStates)
        assertEquals(expected.edges, actual.edges)
        assertEquals(expected.edgesToFinalAccept, actual.edgesToFinalAccept)
        assertEquals(expected.edgesToFinalDead, actual.edgesToFinalDead)
    }
}

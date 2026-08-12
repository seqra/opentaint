package org.opentaint.semgrep.pattern.diff

import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.dataflow.jvm.ap.ifds.taint.PrimitiveTaintExt
import org.opentaint.semgrep.pattern.Formula
import org.opentaint.semgrep.pattern.GeneratedTaintMark
import org.opentaint.semgrep.pattern.ResolvedMetaVarInfo
import org.opentaint.semgrep.pattern.RuleWithMetaVars
import org.opentaint.semgrep.pattern.SemgrepMatchingRule
import org.opentaint.semgrep.pattern.SemgrepRule
import org.opentaint.semgrep.pattern.SemgrepRuleLoadTrace
import org.opentaint.semgrep.pattern.SemgrepTaintLabel
import org.opentaint.semgrep.pattern.SemgrepTaintRule
import org.opentaint.semgrep.pattern.SemgrepTraceEntry.Step
import org.opentaint.semgrep.pattern.conversion.LanguageStrategy
import org.opentaint.semgrep.pattern.conversion.SemgrepRuleAutomataBuilder
import org.opentaint.semgrep.pattern.conversion.taint.RuleConversionCtx
import org.opentaint.semgrep.pattern.conversion.taint.TaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomata
import org.opentaint.semgrep.pattern.conversion.taint.TaintRegisterStateAutomataWithStateVars
import org.opentaint.semgrep.pattern.conversion.taint.createTaintAutomata
import org.opentaint.semgrep.pattern.conversion.taint.generateTaintAutomataEdges
import org.opentaint.semgrep.pattern.conversion.taint.prepareTaintNonSourceRules
import org.opentaint.semgrep.pattern.conversion.taint.prepareTaintSourceRules
import org.opentaint.semgrep.pattern.conversion.taint.safeConvertToTaintRules
import org.opentaint.semgrep.pattern.conversion.taint.taintMark
import org.opentaint.semgrep.pattern.diff.load.ParsedNormalRuleSnapshot

/** The result of independently compiling one structurally unmatched DNF cube. */
data class CompiledCube(
    val source: ContextualCube,
    val variants: List<TaintAutomataEdges>,
)

/**
 * Compiles one DNF cube through the normal action-list, automata and taint-edge pipeline.
 *
 * This class is deliberately a consumer of the conversion API. It is not installed into
 * [org.opentaint.semgrep.pattern.SemgrepRuleLoader] and does not affect normal rule conversion.
 */
class RuleCubeCompiler(
    private val strategy: LanguageStrategy<*, *>,
) {
    fun compile(
        cube: ContextualCube,
        ruleContext: ParsedNormalRuleSnapshot,
        trace: SemgrepRuleLoadTrace,
    ): CompiledCube = compileWithStrategy(cube, ruleContext, trace, strategy.unchecked())

    private fun <P : Any> compileWithStrategy(
        cube: ContextualCube,
        ruleContext: ParsedNormalRuleSnapshot,
        trace: SemgrepRuleLoadTrace,
        strategy: LanguageStrategy<P, *>,
    ): CompiledCube {
        require(ruleContext.descriptor.qualifiedRuleId == cube.ownerRuleId) {
            "Cube owner ${cube.ownerRuleId} does not match rule context " +
                ruleContext.descriptor.qualifiedRuleId
        }

        // Build as a matching rule first. This keeps the expensive parser/rewriter/automata
        // work scoped to this cube; role metadata is applied to each resulting variant below.
        val cubeRule: SemgrepRule<Formula> = SemgrepMatchingRule(listOf(cube.cube.formula))
        val semgrepAutomata = SemgrepRuleAutomataBuilder(strategy).build(cubeRule, trace)
        val taintAutomata = createTaintAutomata(
            semgrepAutomata,
            trace.stepTrace(Step.BUILD_TAINT_AUTOMATA),
            strategy.typeOps,
        ) as SemgrepMatchingRule

        val conversionCtx = RuleConversionCtx(
            ruleId = cube.ownerRuleId,
            modeModifier = if (ruleContext.primitiveTracking) {
                PrimitiveTaintExt.PRIMITIVE_TRACKING_ENABLED_MODE
            } else {
                null
            },
            // Sink metadata is only consumed during final serialized-rule emission, which this
            // standalone compiler intentionally does not perform.
            meta = SinkMetaData(),
            trace = trace.stepTrace(Step.AUTOMATA_TO_TAINT_RULE),
            typeOps = strategy.typeOps,
        )

        val variants = taintAutomata.rules.mapNotNull { built ->
            conversionCtx.safeConvertToTaintRules {
                val withRoleVars = conversionCtx.prepareForContext(
                    built,
                    cube.context,
                    ruleContext.rule,
                )
                conversionCtx.generateTaintAutomataEdges(withRoleVars.rule, withRoleVars.metaVarInfo)
            }
        }

        return CompiledCube(cube, variants)
    }
}

private data class PreparedVariant(
    val rule: TaintRegisterStateAutomataWithStateVars,
    val metaVarInfo: ResolvedMetaVarInfo,
)

private fun RuleConversionCtx.prepareForContext(
    built: RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>,
    context: CubeContext,
    fullRule: SemgrepRule<Formula>,
): PreparedVariant = when (context) {
    CubeContext.Matching -> built.withStateVars()
    is CubeContext.Source -> prepareSource(built, context)
    is CubeContext.Sink -> prepareSink(built, context, fullRule)
    is CubeContext.Propagator -> preparePropagator(built, context, fullRule)
    is CubeContext.Sanitizer -> prepareSanitizer(built, context, fullRule)
    is CubeContext.JoinOperand -> {
        val underlying = prepareForContext(built, context.underlying, fullRule)
        val roleVars = when (context.side) {
            JoinSide.LEFT -> underlying.rule.copy(
                acceptStateVars = underlying.rule.acceptStateVars + context.joinMetaVar
            )
            JoinSide.RIGHT -> underlying.rule.copy(
                initialStateVars = underlying.rule.initialStateVars + context.joinMetaVar
            )
        }
        underlying.copy(rule = roleVars)
    }
}

private fun RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>.withStateVars() =
    PreparedVariant(
        TaintRegisterStateAutomataWithStateVars(
            automata = rule,
            initialStateVars = emptySet(),
            acceptStateVars = emptySet(),
        ),
        metaVarInfo,
    )

private fun RuleConversionCtx.prepareSource(
    built: RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>,
    context: CubeContext.Source,
): PreparedVariant {
    val isolated = SemgrepTaintRule(
        sources = listOf(context.declaration.updatePattern(built)),
        sinks = emptyList(),
        propagators = emptyList(),
        sanitizers = emptyList(),
    )
    val prepared = prepareTaintSourceRules(isolated).first.single().rule
    return PreparedVariant(prepared.rule, prepared.metaVarInfo)
}

private fun RuleConversionCtx.prepareSink(
    built: RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>,
    context: CubeContext.Sink,
    fullRule: SemgrepRule<Formula>,
): PreparedVariant {
    val isolated = SemgrepTaintRule(
        sources = emptyList(),
        sinks = listOf(context.declaration.updatePattern(built)),
        propagators = emptyList(),
        sanitizers = emptyList(),
    )
    val prepared = prepareTaintNonSourceRules(
        isolated,
        sources = emptyList(),
        taintMarks = sourceMarks(fullRule),
    ).sink.single().rule
    return PreparedVariant(prepared.rule, prepared.metaVarInfo)
}

private fun RuleConversionCtx.preparePropagator(
    built: RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>,
    context: CubeContext.Propagator,
    fullRule: SemgrepRule<Formula>,
): PreparedVariant {
    val isolated = SemgrepTaintRule(
        sources = emptyList(),
        sinks = emptyList(),
        propagators = listOf(context.declaration.updatePattern(built)),
        sanitizers = emptyList(),
    )
    val prepared = prepareTaintNonSourceRules(
        isolated,
        sources = emptyList(),
        taintMarks = sourceMarks(fullRule),
    ).pass.single().rule
    return PreparedVariant(prepared.rule, prepared.metaVarInfo)
}

private fun RuleConversionCtx.prepareSanitizer(
    built: RuleWithMetaVars<TaintRegisterStateAutomata, ResolvedMetaVarInfo>,
    context: CubeContext.Sanitizer,
    fullRule: SemgrepRule<Formula>,
): PreparedVariant {
    val isolated = SemgrepTaintRule(
        sources = emptyList(),
        sinks = emptyList(),
        propagators = emptyList(),
        sanitizers = listOf(context.declaration.updatePattern(built)),
    )
    val prepared = prepareTaintNonSourceRules(
        isolated,
        sources = emptyList(),
        taintMarks = sourceMarks(fullRule),
    ).clean.single().rule
    return PreparedVariant(prepared.rule, prepared.metaVarInfo)
}

private fun RuleConversionCtx.sourceMarks(rule: SemgrepRule<Formula>): Set<GeneratedTaintMark> {
    if (rule !is SemgrepTaintRule) return emptySet()
    return rule.sources.mapTo(hashSetOf()) { source ->
        GeneratedTaintMark(taintMark(source.label ?: SemgrepTaintLabel("")))
    }
}

@Suppress("UNCHECKED_CAST")
private fun LanguageStrategy<*, *>.unchecked(): LanguageStrategy<Any, *> =
    this as LanguageStrategy<Any, *>

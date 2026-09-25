package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.ap.ifds.markset.SiteKind
import org.opentaint.dataflow.ap.ifds.taint.TaintAnalysisContext.RuleWithCondition
import org.opentaint.dataflow.configuration.jvm.TaintCleaner
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationItem
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSink
import org.opentaint.dataflow.configuration.jvm.TaintConfigurationSource
import org.opentaint.dataflow.configuration.jvm.TaintPassThrough
import org.opentaint.ir.api.jvm.cfg.JIRInst

/**
 * Records one prescan rule query into the mark-set recorder (spec §4): the statement as covered,
 * then one site per rule with its residual, or the residual's atoms for a cleaner. [rules] are
 * the rewritten rules before `handlePhase()` filters them; false residuals are already dropped.
 *
 * A no-op unless a mark-set recorder is present and active (only during the prescan), so it adds
 * no behaviour when the mark-set scan is off.
 */
internal fun <T : TaintConfigurationItem> JIRTaintAnalysisContext.recordMarkSet(
    statement: JIRInst,
    rules: List<RuleWithCondition<T>>,
) {
    val recorder = markSetRecorder?.takeIf { it.active } ?: return

    recorder.recordStatement(statement)

    for ((rule, condition) in rules) {
        when (rule) {
            is TaintConfigurationSource -> recorder.recordSite(
                statement, rule, SiteKind.SOURCE, condition, rule.actionsAfter.map { it.mark.name }
            )

            is TaintConfigurationSink -> recorder.recordSite(
                statement, rule, SiteKind.SINK, condition, rule.trackFactsReachAnalysisEnd.map { it.mark.name }
            )

            is TaintPassThrough -> recorder.recordSite(
                statement, rule, SiteKind.PASS_THROUGH, condition, emptyList()
            )

            is TaintCleaner -> recorder.recordCleaner(statement, condition)
        }
    }
}

/**
 * Mark-set debug checks (spec §7, E2): observes one full-scan rule query, as [recordMarkSet]
 * records a prescan one. [rules] are the rewritten rules of the unrestricted provider, before the
 * mark-set selection filters them. A no-op unless the recorder is observing (the full scan, with
 * debug checks on).
 */
internal fun <T : TaintConfigurationItem> JIRTaintAnalysisContext.observeMarkSet(
    statement: JIRInst,
    rules: List<RuleWithCondition<T>>,
) {
    val recorder = markSetRecorder?.takeIf { it.observing } ?: return

    for ((rule, condition) in rules) {
        when (rule) {
            is TaintConfigurationSource -> recorder.observeSite(statement, rule, SiteKind.SOURCE, condition)
            is TaintConfigurationSink -> recorder.observeSite(statement, rule, SiteKind.SINK, condition)
            is TaintPassThrough -> recorder.observeSite(statement, rule, SiteKind.PASS_THROUGH, condition)
            is TaintCleaner -> recorder.observeCleaner(statement, condition)
        }
    }
}

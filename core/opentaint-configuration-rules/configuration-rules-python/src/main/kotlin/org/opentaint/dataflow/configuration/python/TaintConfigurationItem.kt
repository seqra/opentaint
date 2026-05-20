package org.opentaint.dataflow.configuration.python

import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSink
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta
import org.opentaint.dataflow.configuration.CommonTaintConfigurationSource

/**
 * In-memory Python taint-rule representation. Built by
 * `org.opentaint.dataflow.python.rules.PIRTaintConfiguration` from the
 * serialized YAML model.
 *
 * Compared with the JVM `TaintConfigurationItem` hierarchy this is intentionally
 * much smaller: Python rules match by string (FQN / regex) rather than against
 * a resolved method, there are no field rules, no method-entry/exit variants,
 * and no `overrides:` flag.
 */
sealed interface TaintConfigurationItem : CommonTaintConfigurationItem {
    val target: Target

    /** [Condition.ConstantTrue] when the rule has no condition. */
    val condition: Condition
}

sealed interface TaintConfigurationSource : TaintConfigurationItem, CommonTaintConfigurationSource {
    val taint: List<TaintAssignAction>
}

sealed interface TaintConfigurationSink : TaintConfigurationItem, CommonTaintConfigurationSink {
    override val meta: TaintSinkMeta
}

sealed interface TaintConfigurationPassThrough : TaintConfigurationItem {
    val copy: List<TaintPassAction>
}

sealed interface TaintConfigurationCleaner : TaintConfigurationItem {
    val cleans: List<TaintCleanAction>

    /** `for: <note>` — scopes the cleaner to sinks whose `meta.note` matches. */
    val forCategory: String?
}

data class TaintEntryPointSource(
    override val target: Target,
    override val condition: Condition,
    override val taint: List<TaintAssignAction>,
) : TaintConfigurationSource

data class TaintSource(
    override val target: Target,
    override val condition: Condition,
    override val taint: List<TaintAssignAction>,
) : TaintConfigurationSource

data class TaintSinkMeta(
    override val message: String,
    override val severity: CommonTaintConfigurationSinkMeta.Severity,
    val cwe: List<Int>?,
    val note: String?,
) : CommonTaintConfigurationSinkMeta

data class TaintSink(
    override val target: Target,
    override val condition: Condition,
    override val id: String,
    override val meta: TaintSinkMeta,
) : TaintConfigurationSink

data class TaintPassThrough(
    override val target: Target,
    override val condition: Condition,
    override val copy: List<TaintPassAction>,
) : TaintConfigurationPassThrough

data class TaintCleaner(
    override val target: Target,
    override val condition: Condition,
    override val cleans: List<TaintCleanAction>,
    override val forCategory: String?,
) : TaintConfigurationCleaner

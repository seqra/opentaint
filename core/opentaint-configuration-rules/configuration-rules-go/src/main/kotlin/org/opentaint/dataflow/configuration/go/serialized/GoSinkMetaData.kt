package org.opentaint.dataflow.configuration.go.serialized

import org.opentaint.dataflow.configuration.CommonTaintConfigurationSinkMeta

data class GoSinkMetaData(
    override val message: String = "",
    override val severity: CommonTaintConfigurationSinkMeta.Severity = CommonTaintConfigurationSinkMeta.Severity.Warning,
    val cwe: List<Int>? = null,
) : CommonTaintConfigurationSinkMeta

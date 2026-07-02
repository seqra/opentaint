package org.opentaint.go.config

import org.opentaint.config.DefaultConfigLoader
import org.opentaint.dataflow.configuration.ConfigurationLoader
import org.opentaint.dataflow.configuration.go.serialized.GoConfigurationLoader
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig

object GoDefaultConfigLoader: DefaultConfigLoader<GoSerializedTaintConfig> {
    override val configRoot: String get() = "/model/go/config"
    override val configLoader: ConfigurationLoader<GoSerializedTaintConfig> get() = GoConfigurationLoader()
}

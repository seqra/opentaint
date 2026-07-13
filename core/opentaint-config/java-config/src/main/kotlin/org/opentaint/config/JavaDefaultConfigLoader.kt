package org.opentaint.config

import org.opentaint.dataflow.configuration.ConfigurationLoader
import org.opentaint.dataflow.configuration.jvm.serialized.JavaConfigurationLoader
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig

object JavaDefaultConfigLoader : DefaultConfigLoader<SerializedTaintConfig> {
    override val configRoot: String get() = "/model/java/config"
    override val configLoader: ConfigurationLoader<SerializedTaintConfig> get() = JavaConfigurationLoader()
}

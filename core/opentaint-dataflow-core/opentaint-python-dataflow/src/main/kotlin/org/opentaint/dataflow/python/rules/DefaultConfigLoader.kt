package org.opentaint.dataflow.python.rules

import org.opentaint.python.config.PythonConfigLoader

fun loadDefaultConfig(): PIRTaintRulesProvider {
    val serialized = PythonConfigLoader.getConfig() ?: error("Error while loading config")
    val taintConfig = PIRTaintConfiguration().apply { loadConfig(serialized) }
    return PIRConfigTaintRulesProvider(taintConfig)
}

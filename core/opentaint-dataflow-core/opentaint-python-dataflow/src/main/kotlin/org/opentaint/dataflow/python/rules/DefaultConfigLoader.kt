package org.opentaint.dataflow.python.rules

import org.opentaint.python.config.PythonDefaultConfigLoader

private val defaultConfig by lazy { PythonDefaultConfigLoader.loadConfig() }

fun loadDefaultConfig(): PIRTaintRulesProvider {
    val serialized = defaultConfig ?: error("Error while loading config")
    val taintConfig = PIRTaintConfiguration().apply { loadConfig(serialized) }
    return PIRConfigTaintRulesProvider(taintConfig)
}

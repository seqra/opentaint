package org.opentaint.dataflow.python.rules

import org.opentaint.python.config.PythonConfigLoader

/**
 * Loads the shipped python taint config via [PythonConfigLoader] and folds it
 * into the in-memory rule representation.
 */
fun loadDefaultConfig(): PIRTaintRulesProvider {
    val serialized = PythonConfigLoader.getConfig() ?: error("Error while loading config")
    val taintConfig = PIRTaintConfiguration().apply { loadConfig(serialized) }
    return PIRConfigTaintRulesProvider(taintConfig)
}

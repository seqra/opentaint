package org.opentaint.dataflow.python.rules

/**
 * Loads the shipped python taint config via [PythonConfigLoader] and folds it
 * into the in-memory rule representation.
 */
fun loadDefaultConfig(): PIRTaintConfiguration {
    val serialized = PythonConfigLoader.getConfig() ?: error("Error while loading config")
    return PIRTaintConfiguration(serialized)
}

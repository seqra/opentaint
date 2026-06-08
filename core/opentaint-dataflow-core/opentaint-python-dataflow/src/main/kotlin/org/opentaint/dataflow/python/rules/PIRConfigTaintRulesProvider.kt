package org.opentaint.dataflow.python.rules

import org.opentaint.ir.api.python.PIRFunction

/**
 * Default [PIRTaintRulesProvider] backed by a single [PIRTaintConfiguration].
 * Thin delegating wrapper, mirroring the JVM `JIRTaintRulesProvider(config)`.
 */
class PIRConfigTaintRulesProvider(private val config: PIRTaintConfiguration) : PIRTaintRulesProvider {
    override fun entryPointSourcesForMethod(method: PIRFunction) = config.entryPointSourcesForMethod(method)
    override fun sourcesForMethod(method: PIRFunction) = config.sourcesForMethod(method)
    override fun sinksForMethod(method: PIRFunction) = config.sinksForMethod(method)
    override fun passThroughForMethod(method: PIRFunction) = config.passThroughForMethod(method)
    override fun cleanersForMethod(method: PIRFunction) = config.cleanersForMethod(method)

    override fun sourcesForAttribute(name: String) = config.sourcesForAttribute(name)
    override fun sinksForAttribute(name: String) = config.sinksForAttribute(name)
    override fun passThroughForAttribute(name: String) = config.passThroughForAttribute(name)
    override fun cleanersForAttribute(name: String) = config.cleanersForAttribute(name)
}

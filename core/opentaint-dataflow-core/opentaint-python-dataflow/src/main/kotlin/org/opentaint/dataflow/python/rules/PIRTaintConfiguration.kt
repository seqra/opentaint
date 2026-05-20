package org.opentaint.dataflow.python.rules

import org.opentaint.dataflow.configuration.python.TaintCleaner
import org.opentaint.dataflow.configuration.python.TaintEntryPointSource
import org.opentaint.dataflow.configuration.python.TaintPassThrough
import org.opentaint.dataflow.configuration.python.TaintSink
import org.opentaint.dataflow.configuration.python.TaintSource
import org.opentaint.dataflow.configuration.python.serialized.SerializedPythonTaintConfig
import org.opentaint.ir.api.python.PIRFunction
import java.util.concurrent.ConcurrentHashMap

/**
 * Per-method / per-attribute Python taint rule lookup. Holds the parsed
 * [SerializedPythonTaintConfig] and delegates to
 * [MethodTaintConfigurationResolver] to compile rules against a
 * concrete [PIRFunction] (or attribute name) on demand. Mirrors the JVM
 * `TaintConfiguration` shape — rules are not materialised eagerly, and
 * the result of each lookup is cached on the matched key.
 */
class PIRTaintConfiguration(private val config: SerializedPythonTaintConfig) {

    private val entryPointsByMethod = ConcurrentHashMap<PIRFunction, List<TaintEntryPointSource>>()
    private val sourcesByMethod = ConcurrentHashMap<PIRFunction, List<TaintSource>>()
    private val sinksByMethod = ConcurrentHashMap<PIRFunction, List<TaintSink>>()
    private val passThroughByMethod = ConcurrentHashMap<PIRFunction, List<TaintPassThrough>>()
    private val cleanersByMethod = ConcurrentHashMap<PIRFunction, List<TaintCleaner>>()

    private val sourcesByAttribute = ConcurrentHashMap<String, List<TaintSource>>()
    private val sinksByAttribute = ConcurrentHashMap<String, List<TaintSink>>()
    private val passThroughByAttribute = ConcurrentHashMap<String, List<TaintPassThrough>>()
    private val cleanersByAttribute = ConcurrentHashMap<String, List<TaintCleaner>>()

    fun entryPointsForMethod(method: PIRFunction): List<TaintEntryPointSource> =
        entryPointsByMethod.cached(method) { MethodTaintConfigurationResolver.resolveEntryPoints(config.entryPoint, method) }

    fun sourcesForMethod(method: PIRFunction): List<TaintSource> =
        sourcesByMethod.cached(method) { MethodTaintConfigurationResolver.resolveSources(config.source, method) }

    fun sinksForMethod(method: PIRFunction): List<TaintSink> =
        sinksByMethod.cached(method) { MethodTaintConfigurationResolver.resolveSinks(config.sink, method) }

    fun passThroughForMethod(method: PIRFunction): List<TaintPassThrough> =
        passThroughByMethod.cached(method) { MethodTaintConfigurationResolver.resolvePassThrough(config.passThrough, method) }

    fun cleanersForMethod(method: PIRFunction): List<TaintCleaner> =
        cleanersByMethod.cached(method) { MethodTaintConfigurationResolver.resolveCleaners(config.cleaner, method) }

    fun sourcesForAttribute(name: String): List<TaintSource> =
        sourcesByAttribute.cached(name) { MethodTaintConfigurationResolver.resolveAttributeSources(config.source, name) }

    fun sinksForAttribute(name: String): List<TaintSink> =
        sinksByAttribute.cached(name) { MethodTaintConfigurationResolver.resolveAttributeSinks(config.sink, name) }

    fun passThroughForAttribute(name: String): List<TaintPassThrough> =
        passThroughByAttribute.cached(name) { MethodTaintConfigurationResolver.resolveAttributePassThrough(config.passThrough, name) }

    fun cleanersForAttribute(name: String): List<TaintCleaner> =
        cleanersByAttribute.cached(name) { MethodTaintConfigurationResolver.resolveAttributeCleaners(config.cleaner, name) }

    /** Canonicalises empty results to the shared [emptyList] singleton to avoid per-key allocations. */
    private inline fun <K : Any, V> ConcurrentHashMap<K, List<V>>.cached(key: K, crossinline resolve: (K) -> List<V>): List<V> =
        computeIfAbsent(key) { resolve(it).ifEmpty { emptyList() } }
}

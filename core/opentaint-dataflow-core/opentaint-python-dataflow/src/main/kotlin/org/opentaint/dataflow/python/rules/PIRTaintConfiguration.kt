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

    fun entryPointSourcesForMethod(method: PIRFunction): List<TaintEntryPointSource> =
        entryPointsByMethod.cached(method) { MethodTaintConfigurationResolver(it).resolveEntryPoints(config.entryPoint) }

    fun sourcesForMethod(method: PIRFunction): List<TaintSource> =
        sourcesByMethod.cached(method) { MethodTaintConfigurationResolver(it).resolveSources(config.source) }

    fun sinksForMethod(method: PIRFunction): List<TaintSink> =
        sinksByMethod.cached(method) { MethodTaintConfigurationResolver(it).resolveSinks(config.sink) }

    fun passThroughForMethod(method: PIRFunction): List<TaintPassThrough> =
        passThroughByMethod.cached(method) { MethodTaintConfigurationResolver(it).resolvePassThrough(config.passThrough) }

    fun cleanersForMethod(method: PIRFunction): List<TaintCleaner> =
        cleanersByMethod.cached(method) { MethodTaintConfigurationResolver(it).resolveCleaners(config.cleaner) }

    fun sourcesForAttribute(name: String): List<TaintSource> =
        sourcesByAttribute.cached(name) { MethodTaintConfigurationResolver(method = null).resolveAttributeSources(config.source, it) }

    fun sinksForAttribute(name: String): List<TaintSink> =
        sinksByAttribute.cached(name) { MethodTaintConfigurationResolver(method = null).resolveAttributeSinks(config.sink, it) }

    fun passThroughForAttribute(name: String): List<TaintPassThrough> =
        passThroughByAttribute.cached(name) { MethodTaintConfigurationResolver(method = null).resolveAttributePassThrough(config.passThrough, it) }

    fun cleanersForAttribute(name: String): List<TaintCleaner> =
        cleanersByAttribute.cached(name) { MethodTaintConfigurationResolver(method = null).resolveAttributeCleaners(config.cleaner, it) }

    /** Canonicalises empty results to the shared [emptyList] singleton to avoid per-key allocations. */
    private inline fun <K : Any, V> ConcurrentHashMap<K, List<V>>.cached(key: K, crossinline resolve: (K) -> List<V>): List<V> =
        computeIfAbsent(key) { resolve(it).ifEmpty { emptyList() } }
}

package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.*
import org.opentaint.ir.go.type.GoIRAnonymousInterfaceType

class GoIRProgramImpl(
    private val declaredPackages: Map<String, GoIRPackage>,
    private val declaredInterfaces: MutableMap<Int, GoIRAnonymousInterfaceType>,
) : GoIRProgram {
    private var transformers: List<GoIRTransformer> = emptyList()

    private val resolvedPackages: Lazy<Map<String, Lazy<GoIRPackage?>>> = lazy {
        val additional = transformers.flatMap { it.additionalPackages }.associateBy { it.importPath }
        (declaredPackages.keys + additional.keys).associateWith { importPath ->
            lazy {
                fun resolve(index: Int): GoIRPackage? = if (index < 0) {
                    declaredPackages[importPath] ?: additional[importPath]
                } else {
                    transformers[index].resolvePackage(importPath) { resolve(index - 1) }
                }
                resolve(transformers.lastIndex)
            }
        }
    }

    /** Installs package lookup interceptors. Must be called before the first package lookup. */
    fun install(transformers: List<GoIRTransformer>) {
        check(!resolvedPackages.isInitialized()) { "Go IR transformers must be installed before package lookup" }
        this.transformers = transformers
    }

    /** The package as it was deserialized, before any transformer. */
    internal fun declaredPackage(importPath: String): GoIRPackage? = declaredPackages[importPath]

    internal fun addAnonymousInterface(type: GoIRAnonymousInterfaceType) {
        check(declaredInterfaces.putIfAbsent(type.id, type) == null) { "Anonymous interface ${type.id} already exists" }
    }

    override val anonymousInterfaces: Map<Int, GoIRAnonymousInterfaceType> get() = declaredInterfaces

    override val packages: Map<String, GoIRPackage> by lazy {
        if (transformers.isEmpty()) return@lazy declaredPackages
        object : AbstractMap<String, GoIRPackage>() {
            override fun get(key: String): GoIRPackage? = resolvedPackages.value[key]?.value
            override fun containsKey(key: String): Boolean = get(key) != null
            override val entries: Set<Map.Entry<String, GoIRPackage>> by lazy {
                resolvedPackages.value.entries
                    .mapNotNull { (importPath, pkg) -> pkg.value?.let { java.util.AbstractMap.SimpleEntry(importPath, it) } }
                    .toSet()
            }
        }
    }

    override fun findPackage(importPath: String) = packages[importPath]

    override fun allFunctions(): List<GoIRFunction> =
        packages.values.flatMap { it.functions }

    override fun allNamedTypes(): List<GoIRNamedType> =
        packages.values.flatMap { it.namedTypes }

    override fun mainPackage(): GoIRPackage? =
        packages.values.find { it.name == "main" }
}

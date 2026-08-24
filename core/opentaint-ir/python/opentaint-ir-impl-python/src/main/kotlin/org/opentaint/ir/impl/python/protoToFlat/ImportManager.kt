package org.opentaint.ir.impl.python.protoToFlat

internal sealed interface ImportBinding {
    data class Module(val name: String) : ImportBinding {
        init {
            require('.' !in name) { "Module.name must be a single segment, got '$name'" }
        }
    }
    data class Attr(val parent: ImportBinding, val name: String) : ImportBinding {
        init {
            require('.' !in name) { "Attr.name must be a single segment, got '$name'" }
        }
    }
    data class BareGlobal(val name: String) : ImportBinding
}

internal class ImportManager(private val parent: ImportManager? = null) {

    private val bindings = mutableMapOf<String, ImportBinding>()

    fun recordImport(module: String, alias: String) {
        val bound: String
        val binding: ImportBinding
        if (alias.isNotEmpty()) {
            bound = alias
            binding = moduleChain(module)
        } else {
            bound = module.substringBefore('.')
            binding = ImportBinding.Module(bound)
        }
        bindings[bound] = binding
    }

    /**
     * [module] is the already-resolved absolute module path.
     * An empty [module] (mypy errored) binds a [ImportBinding.BareGlobal].
     */
    fun recordImportFrom(module: String, name: String, alias: String) {
        require(name.isNotEmpty()) { "recordImportFrom: `name` must not be empty" }
        val bound = alias.ifEmpty { name }
        bindings[bound] = if (module.isEmpty()) {
            ImportBinding.BareGlobal(name)
        } else {
            ImportBinding.Attr(moduleChain(module), name)
        }
    }

    fun resolve(name: String): ImportBinding? {
        bindings[name]?.let { return it }
        return parent?.resolve(name)
    }

    fun nestedChild(): ImportManager = ImportManager(parent = this)
}

internal fun moduleChain(dottedPath: String): ImportBinding {
    require(dottedPath.isNotEmpty()) {
        "Dotted path must be non-empty"
    }

    val segments = dottedPath.split(".")
    var node: ImportBinding = ImportBinding.Module(segments.first())
    for (i in 1 until segments.size) {
        node = ImportBinding.Attr(node, segments[i])
    }
    return node
}

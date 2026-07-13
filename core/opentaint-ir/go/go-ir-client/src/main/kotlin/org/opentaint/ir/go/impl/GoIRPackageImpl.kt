package org.opentaint.ir.go.impl

import org.opentaint.ir.go.api.GoIRConst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRGlobal
import org.opentaint.ir.go.api.GoIRNamedType
import org.opentaint.ir.go.api.GoIRPackage

class GoIRPackageImpl(
    override val importPath: String,
    override val name: String,
    override val isStdlib: Boolean = false,
    override val isDependency: Boolean = false,
) : GoIRPackage {
    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is GoIRPackage) return false
        return importPath == other.importPath
    }

    override fun hashCode(): Int = importPath.hashCode()

    // Functions are stored as a list because methods on different named types
    // legitimately share the same short name (e.g. `Legs` on both `Dog` and
    // `Snake`), so a map keyed by `fn.name` would drop declarations.
    private val _functions = mutableListOf<GoIRFunction>()
    private val _namedTypes = mutableMapOf<String, GoIRNamedType>()
    private val _globals = mutableMapOf<String, GoIRGlobal>()
    private val _constants = mutableMapOf<String, GoIRConst>()
    val _imports = mutableListOf<GoIRPackage>()

    override val functions: List<GoIRFunction> get() = _functions
    override val namedTypes: List<GoIRNamedType> get() = _namedTypes.values.toList()
    override val globals: List<GoIRGlobal> get() = _globals.values.toList()
    override val constants: List<GoIRConst> get() = _constants.values.toList()
    override val imports: List<GoIRPackage> get() = _imports
    override var initFunction: GoIRFunction? = null

    fun addFunction(fn: GoIRFunction) {
        _functions.add(fn)
    }

    fun addNamedType(nt: GoIRNamedType) { _namedTypes[nt.name] = nt }
    fun addGlobal(g: GoIRGlobal) { _globals[g.name] = g }
    fun addConst(c: GoIRConst) { _constants[c.name] = c }

    override fun findNamedType(name: String) = _namedTypes[name]
    override fun findGlobal(name: String) = _globals[name]
    override fun findConstant(name: String) = _constants[name]

    override fun allMethods(): List<GoIRFunction> =
        namedTypes.flatMap { it.allMethods() }

    override fun toString(): String = "GoIRPackage($importPath)"
}

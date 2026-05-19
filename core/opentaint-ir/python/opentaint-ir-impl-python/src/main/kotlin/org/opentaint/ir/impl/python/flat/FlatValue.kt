package org.opentaint.ir.impl.python.flat

/**
 * Operand of a [FlatInst]. Either a constant or a local/temporary variable.
 *
 * Name resolution is **not** a value: globals and modules are referenced by
 * [FlatNameRef] inside dedicated instructions ([FlatReadName] for reads,
 * [FlatStoreGlobal] / [FlatDeleteGlobal] for writes, [FlatBindFunction] for
 * the structural reference to a lifted function). This keeps every
 * `FlatValue` operand uniformly "local or const", making instruction shape
 * legible from types alone.
 */
sealed interface FlatValue

data class FlatLocal(val name: String, val type: FlatType = FlatAnyType) : FlatValue

/**
 * Reference to a function parameter, identified by [name].
 *
 * Emitted by the parameter-binding prologue inserted at function entry —
 * each parameter `p` becomes one `FlatAssign(FlatLocal("p"),
 * FlatParameterRef("p"))` instruction in block 0, after which the body
 * reads/writes the same-named local — and by the closure rewriter's
 * prologue when reading the synthetic `<self>` env parameter on capturing
 * children. This keeps the body lowering representation-uniform (mypy
 * itself doesn't distinguish parameter-vs-local at the use site) while
 * giving downstream passes a structural marker for parameter slots.
 *
 * No index is stored: the closure rewriter prepends a `<self>` parameter
 * to capturing children, which would shift every other parameter's index
 * post-rewrite. Consumers that need an index recover it by name lookup
 * against the function's [FlatParameter] list at point of use.
 */
data class FlatParameterRef(
    val name: String,
    val type: FlatType = FlatAnyType,
) : FlatValue

sealed interface FlatConst : FlatValue
data class FlatIntConst(val value: Long) : FlatConst
data class FlatFloatConst(val value: Double) : FlatConst
data class FlatStrConst(val value: String) : FlatConst
data class FlatBoolConst(val value: Boolean) : FlatConst
data object FlatNoneConst : FlatConst
data object FlatEllipsisConst : FlatConst
data class FlatBytesConst(val value: ByteArray) : FlatConst {
    override fun equals(other: Any?) = this === other || (other is FlatBytesConst && value.contentEquals(other.value))
    override fun hashCode() = value.contentHashCode()
}
data class FlatComplexConst(val real: Double, val imag: Double) : FlatConst

// ─── Name references (NOT values) ───────────────────────────

/**
 * A structural name that the IR must resolve at runtime. Carried by
 * [FlatReadName] (read), [FlatStoreGlobal] / [FlatDeleteGlobal]
 * (write/delete of a global), and [FlatBindFunction] (structural reference
 * to a lifted function). Not a [FlatValue]: resolution is a side-effecting
 * load, distinct from an operand read, so every use site spills it through
 * a `FlatReadName` into a local first.
 */
sealed interface FlatNameRef

/**
 * Reference to a globally-resolvable name, identified by its canonical
 * qualified name. For intra-module functions [qualifiedName] equals the
 * corresponding [FlatFunctionIR.qualifiedName]; for builtins / cross-module
 * imports it is the canonical dotted fullname (`builtins.AssertionError`,
 * `os.getcwd`).
 */
data class FlatGlobalNameRef(val qualifiedName: String) : FlatNameRef

/**
 * Reference to an entire module by its top-level segment (e.g. `os` in
 * `os.getcwd()`, or the root `collections` of `from collections.abc
 * import Iterable`). Distinct from [FlatGlobalNameRef], which names a
 * value defined inside a module.
 *
 * `module` is a single segment with no dots — sub-module access (e.g.
 * `os.path` reached via `import os.path as p`, or `collections.abc`
 * reached via `from collections.abc import Iterable`) is uniformly
 * represented as a `FlatLoadAttr` chain rooted at the local that received
 * a `FlatReadName(_, FlatModuleNameRef(...))`. Aliases are resolved at
 * lowering time so downstream consumers only ever see the canonical root
 * segment.
 */
data class FlatModuleNameRef(val module: String) : FlatNameRef {
    init {
        require('.' !in module) { "FlatModuleNameRef.module must be a single segment, got '$module'" }
    }
}

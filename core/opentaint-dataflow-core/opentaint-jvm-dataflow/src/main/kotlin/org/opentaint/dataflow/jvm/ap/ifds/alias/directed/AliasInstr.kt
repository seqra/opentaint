package org.opentaint.dataflow.jvm.ap.ifds.alias.directed

/**
 * A value expression of the engine. The transfer evaluates it with the `Assign` rules of IMPL §4.1.
 * A stored value uses the same rules, with the site of the store (`value(v)`).
 * A primitive value is not a value expression: the lowering drops it.
 */
sealed interface AliasValue {

    /** A value that the transfer reads from the state: a local, `this`, or an argument. */
    sealed interface Ref : AliasValue

    /** A local. Its value is `env[v]`. */
    data class Local(val v: VarId) : Ref

    /** `this`. Its value is `{Sym(THIS)}` by rule. It is not in `env`. */
    data object This : Ref

    /** Argument [index]. Its value is `{Sym(ARG(index))}` by rule. It is not in `env`. */
    data class Arg(val index: Int) : Ref

    /** `new` or `newarray` at [site]: `retire(site)` (loop sites only), then `{AllocNew(site)}`. */
    data class New(val site: SiteId) : AliasValue

    /** A catch variable, another allocation, or an unknown expression at [site]: `{Sym(FRESH(site))}`. */
    data class Fresh(val site: SiteId) : AliasValue

    /** A box of a value that is not a constant at [site]: `{Sym(BOX(site))}` (I3). */
    data class Box(val site: SiteId) : AliasValue

    /** The null constant at [site]: `{Sym(NULL(site))}`. */
    data class Null(val site: SiteId) : AliasValue

    /**
     * An interned constant: `{Sym(CONST(key))}`. [base] is a `CONST` base of [BaseTable]: a string
     * (value), a class literal (class name), a box of a constant (box type and constant text), or
     * another constant (type and text).
     */
    data class Const(val base: BaseId) : AliasValue
}

/**
 * An instruction of the engine (IMPL §4.1). The lowering of JIR statements makes these
 * instructions. The payloads are ids of [AliasTables].
 */
sealed interface AliasInstr {

    /**
     * `dst = value`. It covers the rows `Copy`, `Assign(Alloc(new / newarray))`, `Assign(Alloc(catch))`,
     * `Assign(Alloc(box valueOf))`, `Assign(Alloc(other))`, `Assign(Unknown)` and `Assign(RefConst)`.
     */
    data class Assign(val dst: VarId, val value: AliasValue) : AliasInstr

    /** `dst = C.f`: `{Sym(STATIC(C), [cell])}`. [staticBase] is a `STATIC` base of [BaseTable]. */
    data class StaticRead(val dst: VarId, val staticBase: BaseId, val cell: CellId) : AliasInstr

    /** `dst = base.f`: `env[dst] := load(val(base), cell)`. */
    data class FieldLoad(val dst: VarId, val base: AliasValue.Ref, val cell: CellId) : AliasInstr

    /** `dst = base[i]`: `env[dst] := load(val(base), ELEM_CELL)`. */
    data class ArrayLoad(val dst: VarId, val base: AliasValue.Ref) : AliasInstr

    /** `base.f = value`: `store(val(base), cell, value(value))`. */
    data class FieldStore(val base: AliasValue.Ref, val cell: CellId, val value: AliasValue) : AliasInstr

    /** `base[i] = value`: `storeWeak(val(base), ELEM_CELL, value(value))`. */
    data class ArrayStore(val base: AliasValue.Ref, val value: AliasValue) : AliasInstr

    /** `C.f = value`: no change (A5). */
    data object StaticWrite : AliasInstr

    /**
     * `return value` ([value] is `null` for a `void` return or a primitive value). No change in the
     * analyzed method. An inlined callee gives the value to the result of the call (IMPL §5.5).
     */
    data class Return(val value: AliasValue?) : AliasInstr

    /** `throw value`: no change. */
    data class Throw(val value: AliasValue.Ref) : AliasInstr

    /** An instruction with no effect on the alias state. */
    data object Nop : AliasInstr

    /**
     * An unresolved call at [site] (IMPL §4.4). [args] has the receiver first, if the call has one.
     * For an unresolved `<init>`, the receiver is the new object. [models] are the pass-through
     * models of the callee (IMPL §4.5), in their order. [DirectedFixpoint] evaluates it ([AliasCall]).
     */
    data class UnresolvedCall(
        val site: SiteId,
        val result: VarId?,
        val args: List<AliasValue>,
        val models: List<PassThrough> = emptyList(),
    ) : AliasInstr

    /**
     * A resolved call at [site] (IMPL §5.5). [args] has the receiver first, if the call has one.
     * [callees] gives the CFG of each override with a body. [DirectedFixpoint] inlines each override
     * from the state before the call. If no override gives a return state, it uses the rule of the
     * unresolved call with the pass-through [models] (IMPL §4.4, §4.5), as main does.
     */
    data class ResolvedCall(
        val site: SiteId,
        val result: VarId?,
        val args: List<AliasValue>,
        val models: List<PassThrough> = emptyList(),
        val callees: CalleeBodies = CalleeBodies.NONE,
    ) : AliasInstr
}

/**
 * The bodies of the overrides of a resolved call (IMPL §5.5). The JIR adapter makes them: each body
 * has its own context, and its `this` and its arguments are the values of the call.
 *
 * [AliasCfg.callees] calls [build] one time for each call statement, before the first run of the
 * bodies, and keeps the result. [build] marks the loop sites of the bodies (IMPL §5.4): if
 * `callOnCycle` is true, the call is on a cycle of the caller (or of a caller of the caller), and
 * each site of the bodies is a loop site.
 */
fun interface CalleeBodies {
    /** The CFG of each override with a body. An empty list: the call has no body to inline. */
    fun build(callOnCycle: Boolean): List<AliasCfg>

    companion object {
        /** No body: the call uses the rule of the unresolved call. */
        val NONE: CalleeBodies = CalleeBodies { emptyList() }
    }
}

/**
 * A pass-through model of an unresolved call (IMPL §4.5, spec §5.6): after the call, a weak copy
 * `to ∪= pts(from)`. The lowering makes it from an `ExternalAssign` of `ExternalCallModelProvider`.
 */
data class PassThrough(val from: ModelPath, val to: ModelPath)

/** A position of a pass-through model: a base value and a path of cells below it. */
data class ModelPath(val base: ModelBase, val cells: List<CellId> = emptyList())

/** The base of a [ModelPath]. */
sealed interface ModelBase {

    /** The result variable of the call. */
    data object Result : ModelBase

    /** A value of the call: an argument or the receiver. */
    data class Value(val value: AliasValue) : ModelBase
}

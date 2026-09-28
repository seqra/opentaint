package org.opentaint.dataflow.jvm.ap.ifds.analysis

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasApInfo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.Access
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.MemoryAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.RefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.StaticRefAccess
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.clearField
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.mayReadAccessor
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.mayRemoveAfterWrite
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.readAccessorTo
import org.opentaint.dataflow.jvm.ap.ifds.MethodFlowFunctionUtils.writeToAccessor
import org.opentaint.ir.api.jvm.JIRType
import org.opentaint.ir.api.jvm.cfg.JIRArrayAccess
import org.opentaint.ir.api.jvm.cfg.JIRAssignInst
import org.opentaint.ir.api.jvm.cfg.JIRBinaryExpr
import org.opentaint.ir.api.jvm.cfg.JIRCastExpr
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRFieldRef
import org.opentaint.ir.api.jvm.cfg.JIRImmediate
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.cfg.JIRValue

class JIRAssignTransfer(
    private val direction: Direction,
    private val analysisContext: JIRMethodAnalysisContext,
    private val statement: JIRInst,
) {
    enum class Direction { FORWARD, BACKWARD }

    private class Flow(
        val unchanged: (FinalFactAp) -> Unit,
        val propagate: (FinalFactAp) -> Unit,
        val exclude: (FinalFactAp, Accessor) -> Unit,
    ) {
        fun skipping(
            base: AccessPathBase,
            onPropagate: (FinalFactAp) -> Unit = {},
            onExclude: (FinalFactAp, Accessor) -> Unit = { _, _ -> },
        ) = Flow(
            unchanged = { if (it.base != base) unchanged(it) },
            propagate = { if (it.base != base) propagate(it) else onPropagate(it) },
            exclude = { f, a -> if (f.base != base) exclude(f, a) else onExclude(f, a) },
        )

        fun prepending(accessor: Accessor) = Flow(
            unchanged = { unchanged(it.prependAccessor(accessor)) },
            propagate = { propagate(it.prependAccessor(accessor)) },
            exclude = { f, a -> exclude(f.prependAccessor(accessor), a) },
        )
    }

    private val factTypeChecker get() = analysisContext.factTypeChecker
    private val aliasAnalysis get() = analysisContext.aliasAnalysis

    fun assign(
        inst: JIRAssignInst,
        edge: JIRSequentEdge,
        staticRead: ((FinalFactAp, FinalFactAp) -> Unit)? = null,
    ) = assign(inst.rhv, inst.lhv, edge.current, edge, staticRead)

    private fun assign(
        assignFrom: JIRExpr,
        assignTo: JIRValue,
        fact: FinalFactAp,
        edge: JIRSequentEdge,
        staticRead: ((FinalFactAp, FinalFactAp) -> Unit)?,
    ) {
        if (assignFrom is JIRBinaryExpr) {
            assign(assignFrom.lhv, assignTo, fact, edge, staticRead)
            assign(assignFrom.rhv, assignTo, fact, edge, staticRead)
            return
        }

        var filtered = fact
        val fromAccess = assignedValue(assignFrom)?.let { value ->
            val access = MethodFlowFunctionUtils.mkAccess(value) ?: return
            filtered = access.filterFactBaseType(assignFrom, filtered) ?: return
            access
        }

        if (assignTo !is JIRImmediate && assignTo !is JIRArrayAccess && assignTo !is JIRFieldRef) {
            error("Assign to complex value: $assignTo")
        }

        val toAccess = MethodFlowFunctionUtils.mkAccess(assignTo) ?: return
        filtered = toAccess.filterFactBaseType(assignTo, filtered) ?: return

        val propagate: (FinalFactAp) -> Unit = { edge.propagate(it) }
        val exclude: (FinalFactAp, Accessor) -> Unit = { f, a -> edge.propagateExcluded(f, a) }
        val flow = when (direction) {
            Direction.FORWARD -> {
                val unchanged: (FinalFactAp) -> Unit = if (filtered != fact) propagate else { _ -> edge.unchanged() }
                Flow(unchanged, propagate, exclude)
            }

            Direction.BACKWARD -> {
                val keep: (FinalFactAp) -> Unit = { if (it == fact) edge.unchanged() else edge.propagate(it) }
                Flow(keep, keep, exclude)
            }
        }

        when {
            fromAccess is MemoryAccess -> {
                check(toAccess !is MemoryAccess) { "Complex assignment: $assignTo = $assignFrom" }
                when (direction) {
                    Direction.FORWARD -> forwardRead(toAccess.base, fromAccess, filtered, flow)
                    Direction.BACKWARD -> backwardRead(toAccess.base, fromAccess, filtered, flow, staticRead)
                }
            }

            toAccess is MemoryAccess -> when (direction) {
                Direction.FORWARD -> forwardWrite(toAccess, fromAccess?.base, filtered, flow)
                Direction.BACKWARD -> backwardWrite(toAccess, fromAccess?.base, filtered, flow)
            }

            else -> assignBase(toAccess.base, fromAccess?.base, filtered, flow.unchanged, flow.propagate)
        }
    }

    fun assignBase(
        assignTo: AccessPathBase,
        assignFrom: AccessPathBase?,
        fact: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        propagate: (FinalFactAp) -> Unit,
    ) {
        if (assignTo == assignFrom) {
            unchanged(fact)
            return
        }

        if (assignTo != fact.base) {
            unchanged(fact)
        }

        when (direction) {
            Direction.FORWARD -> if (assignFrom == fact.base) {
                propagate(fact.rebase(assignTo))
            }

            Direction.BACKWARD -> if (assignTo == fact.base && assignFrom != null && assignFrom !is AccessPathBase.Constant) {
                propagate(fact.rebase(assignFrom))
            }
        }
    }

    private fun Access.filterFactBaseType(value: JIRExpr, fact: FinalFactAp): FinalFactAp? =
        valueTypes(value).fold(fact) { f, type -> filterFactBaseType(type, f) ?: return null }

    private fun valueTypes(value: JIRExpr): List<JIRType?> = when (value) {
        is JIRCastExpr -> listOf(value.type)
        is JIRImmediate -> listOf(value.type)
        is JIRArrayAccess -> listOf(value.array.type)
        is JIRFieldRef -> listOf(value.instance?.type, value.field.enclosingType)
        else -> emptyList()
    }

    private fun Access.filterFactBaseType(expectedType: JIRType?, factAp: FinalFactAp): FinalFactAp? {
        if (factAp.base != this.base || expectedType == null) return factAp
        return factTypeChecker.filterFactByLocalType(expectedType, factAp)
    }

    private fun forwardRead(assignTo: AccessPathBase, access: MemoryAccess, fact: FinalFactAp, flow: Flow) {
        when (access) {
            is RefAccess -> forwardRead(assignTo, access.base, access.accessor, fact, flow)

            is StaticRefAccess -> {
                val auxiliaryBase = auxiliaryBase()
                val fieldFlow = flow.skipping(auxiliaryBase, onExclude = { _, a -> flow.exclude(fact, a) })
                val classFlow = flow.skipping(auxiliaryBase, onPropagate = {
                    forwardRead(assignTo, auxiliaryBase, access.accessor, it, fieldFlow)
                })
                forwardRead(auxiliaryBase, access.base, access.classStaticAccessor, fact, classFlow)
            }
        }
    }

    private fun forwardRead(
        assignTo: AccessPathBase,
        instance: AccessPathBase,
        accessor: Accessor,
        fact: FinalFactAp,
        flow: Flow,
    ) = readField(
        assignTo, instance, accessor, fact,
        keep = {
            if (assignTo != it.base) {
                if (accessor !is ElementAccessor) flow.unchanged(it) else flow.propagate(it)
            }
        },
        read = flow.propagate,
        excluded = excludedWithAliases(accessor, flow),
    )

    private fun forwardWrite(access: MemoryAccess, assignFrom: AccessPathBase?, fact: FinalFactAp, flow: Flow) {
        val instance = access.base
        if (assignFrom == instance) {
            if (fact.base != instance) {
                flow.unchanged(fact)
                return
            }

            val auxiliaryBase = auxiliaryBase()
            check(auxiliaryBase != instance)

            val auxiliaryFlow = flow.skipping(auxiliaryBase)
            forwardWrite(access, auxiliaryBase, fact.rebase(auxiliaryBase), auxiliaryFlow)
            forwardWrite(access, auxiliaryBase, fact, auxiliaryFlow)
            return
        }

        if (fact.base == assignFrom) {
            flow.unchanged(fact)

            val written = fact.writeToAccess(access)
            flow.propagate(written)
            aliasAnalysis?.forEachAliasAtStatement(statement, written) { aliased ->
                flow.propagate(aliased)
            }
            return
        }

        if (fact.base == instance && access.accessor is ElementAccessor) {
            flow.propagate(fact)
            return
        }

        clearField(instance, access.accessor, fact, flow.unchanged, flow.propagate, excludedWithAliases(access.accessor, flow))
    }

    private fun backwardRead(
        assignTo: AccessPathBase,
        access: MemoryAccess,
        fact: FinalFactAp,
        flow: Flow,
        staticRead: ((FinalFactAp, FinalFactAp) -> Unit)?,
    ) {
        if (fact.base != assignTo) {
            flow.unchanged(fact)
            return
        }

        val read = fact.writeToAccess(access)
        if (access is StaticRefAccess && staticRead != null) {
            staticRead(fact, read)
        } else {
            flow.propagate(read)
        }
    }

    private fun backwardWrite(access: MemoryAccess, assignFrom: AccessPathBase?, fact: FinalFactAp, flow: Flow) {
        val value = assignFrom?.takeUnless { it is AccessPathBase.Constant }
        val instance = access.base
        val accessor = access.accessor

        if (fact.base == instance && accessor !is ElementAccessor) {
            strongWrite(access.accessors, value, fact, flow, flow.propagate)
            return
        }

        flow.unchanged(fact)
        if (access !is RefAccess) return

        if (fact.base == instance) {
            readField(value, instance, accessor, fact, keep = {}, read = flow.propagate) { flow.exclude(it, accessor) }
            return
        }

        forEachWriteAlias(instance, fact, flow) { aliased ->
            readField(value, instance, accessor, aliased, keep = {}, read = flow.propagate) { flow.exclude(fact, accessor) }
        }
    }

    private fun strongWrite(
        accessors: List<Accessor>,
        value: AccessPathBase?,
        fact: FinalFactAp,
        flow: Flow,
        moved: (FinalFactAp) -> Unit,
    ) {
        val accessor = accessors.first()
        val instance = fact.base
        val excluded: (FinalFactAp) -> Unit = { flow.exclude(it, accessor) }

        clearField(instance, accessor, fact, flow.unchanged, flow.propagate, excluded)

        val rest = accessors.drop(1)
        if (rest.isEmpty()) {
            readField(value, instance, accessor, fact, keep = {}, read = moved, excluded = excluded)
        } else {
            readField(instance, instance, accessor, fact, keep = {}, excluded = excluded, read = {
                strongWrite(rest, value, it, flow.prepending(accessor), moved)
            })
        }
    }

    private fun readField(
        assignTo: AccessPathBase?,
        instance: AccessPathBase,
        accessor: Accessor,
        fact: FinalFactAp,
        keep: (FinalFactAp) -> Unit,
        read: (FinalFactAp) -> Unit,
        excluded: (FinalFactAp) -> Unit,
    ) {
        keep(fact)

        if (!fact.mayReadAccessor(instance, accessor)) return

        if (fact.isAbstract() && accessor !in fact.exclusions) {
            fact.removeAbstraction()?.let { readField(assignTo, instance, accessor, it, keep, read, excluded) }
            excluded(fact.abstractOnly())
            return
        }

        check(fact.startsWithAccessor(accessor))

        if (assignTo != null) {
            read(fact.readAccessorTo(newBase = assignTo, accessor = accessor))
        }
    }

    private fun clearField(
        instance: AccessPathBase,
        accessor: Accessor,
        fact: FinalFactAp,
        unchanged: (FinalFactAp) -> Unit,
        cleared: (FinalFactAp) -> Unit,
        excluded: (FinalFactAp) -> Unit,
    ) {
        if (!fact.mayRemoveAfterWrite(instance, accessor)) {
            unchanged(fact)
            return
        }

        if (fact.isAbstract() && accessor !in fact.exclusions) {
            fact.removeAbstraction()?.let { clearField(instance, accessor, it, unchanged, cleared, excluded) }
            excluded(fact.abstractOnly())
            return
        }

        check(fact.startsWithAccessor(accessor))

        fact.clearField(accessor)?.let(cleared)
    }

    private fun excludedWithAliases(accessor: Accessor, flow: Flow): (FinalFactAp) -> Unit = { abstractAp ->
        flow.exclude(abstractAp, accessor)
        aliasAnalysis?.forEachAliasAtStatement(statement, abstractAp) { aliased ->
            flow.exclude(aliased, accessor)
        }
    }

    private inline fun forEachWriteAlias(
        instance: AccessPathBase,
        fact: FinalFactAp,
        flow: Flow,
        body: (FinalFactAp) -> Unit,
    ) {
        val instanceLocal = instance as? AccessPathBase.LocalVar ?: return
        val aliases = aliasAnalysis?.findAlias(instanceLocal, statement) ?: return

        for (alias in aliases) {
            if (alias !is AliasApInfo || alias.base != fact.base) continue

            var aliased: FinalFactAp? = fact
            for (aliasAccessor in alias.accessors) {
                val current = aliased ?: break
                val accessor = aliasAccessor.apAccessor()
                if (current.isAbstract() && accessor !in current.exclusions) {
                    flow.exclude(fact, accessor)
                }
                aliased = current.readAccessor(accessor)
            }

            aliased?.let { body(it.rebase(instance)) }
        }
    }

    private fun auxiliaryBase() = AccessPathBase.LocalVar.create(-1)

    private fun assignedValue(expr: JIRExpr): JIRValue? = when (expr) {
        is JIRCastExpr -> expr.operand
        is JIRImmediate -> expr
        is JIRArrayAccess -> expr
        is JIRFieldRef -> expr
        else -> null
    }

    private val MemoryAccess.accessor: Accessor
        get() = when (this) {
            is RefAccess -> accessor
            is StaticRefAccess -> accessor
        }

    private val MemoryAccess.accessors: List<Accessor>
        get() = when (this) {
            is RefAccess -> listOf(accessor)
            is StaticRefAccess -> listOf(classStaticAccessor, accessor)
        }

    private fun FinalFactAp.writeToAccess(access: MemoryAccess): FinalFactAp =
        access.accessors.foldRight(this) { accessor, fact -> fact.writeToAccessor(access.base, accessor) }
}

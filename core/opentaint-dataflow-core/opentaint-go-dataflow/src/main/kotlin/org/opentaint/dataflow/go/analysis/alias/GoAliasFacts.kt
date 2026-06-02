package org.opentaint.dataflow.go.analysis.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo

sealed interface GoRefValue : Comparable<GoRefValue> {
    val valueKind: Int
    fun compareValue(other: GoRefValue): Int

    override fun compareTo(other: GoRefValue): Int {
        val k = valueKind.compareTo(other.valueKind)
        if (k != 0) return k
        return compareValue(other)
    }

    data class Local(val idx: Int, val ctx: ContextInfo) : GoRefValue {
        override val valueKind: Int get() = 0
        override fun compareValue(other: GoRefValue): Int {
            other as Local
            val c = idx.compareTo(other.idx)
            if (c != 0) return c
            return ctx.compareTo(other.ctx)
        }
    }

    data class Arg(val idx: Int) : GoRefValue {
        override val valueKind: Int get() = 1
        override fun compareValue(other: GoRefValue): Int = idx.compareTo((other as Arg).idx)
    }

    data class Global(val name: String) : GoRefValue {
        override val valueKind: Int get() = 2
        override fun compareValue(other: GoRefValue): Int = name.compareTo((other as Global).name)
    }
}

data class GoUnknown(val inst: Int, override val ctx: ContextInfo) : AAInfo {
    override val infoKind: Int get() = 3
    override fun compareInfo(other: AAInfo): Int = inst.compareTo((other as GoUnknown).inst)
}

data class GoReturnValue(val callInst: Int, override val ctx: ContextInfo) : AAInfo {
    override val infoKind: Int get() = 1
    override fun compareInfo(other: AAInfo): Int = callInst.compareTo((other as GoReturnValue).callInst)
}

sealed interface GoLocalAlias : AAInfo {
    data class SimpleLoc(val loc: GoRefValue) : GoLocalAlias {
        override val infoKind: Int get() = 2
        override val ctx: ContextInfo
            get() = if (loc is GoRefValue.Local) loc.ctx else ContextInfo.rootContext
        override fun compareInfo(other: AAInfo): Int = loc.compareTo((other as SimpleLoc).loc)
    }

    data class Alloc(val inst: Int, override val ctx: ContextInfo) : GoLocalAlias {
        override val infoKind: Int get() = 0
        override fun compareInfo(other: AAInfo): Int = inst.compareTo((other as Alloc).inst)
    }
}

sealed interface GoAliasAccessor {
    data class Field(val className: String, val fieldName: String, val fieldType: String) : GoAliasAccessor
    data object Array : GoAliasAccessor
    data object Ref : GoAliasAccessor
}

data class GoFieldAlias(
    val field: GoAliasAccessor.Field,
    override val isImmutable: Boolean,
) : AAHeapAccessor {
    override val accessorKind: Int get() = 0
    override fun compareAccessor(accessor: AAHeapAccessor): Int {
        accessor as GoFieldAlias
        val c = isImmutable.compareTo(accessor.isImmutable)
        if (c != 0) return c
        val c2 = field.fieldName.compareTo(accessor.field.fieldName)
        if (c2 != 0) return c2
        val c3 = field.className.compareTo(accessor.field.className)
        if (c3 != 0) return c3
        return field.fieldType.compareTo(accessor.field.fieldType)
    }
}

data object GoArrayAlias : AAHeapAccessor {
    override val isImmutable: Boolean get() = false
    override val accessorKind: Int get() = 1
    override fun compareAccessor(accessor: AAHeapAccessor): Int = 0
}

data object GoRefAlias : AAHeapAccessor {
    override val isImmutable: Boolean get() = false
    override val accessorKind: Int get() = 2
    override fun compareAccessor(accessor: AAHeapAccessor): Int = 0
}

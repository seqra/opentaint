package org.opentaint.dataflow.jvm.ap.ifds.alias

import org.opentaint.dataflow.ap.ifds.analysis.alias.AAHeapAccessor
import org.opentaint.dataflow.ap.ifds.analysis.alias.AAInfo
import org.opentaint.dataflow.ap.ifds.analysis.alias.ContextInfo
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis.AliasAccessor

data class Unknown(val stmt: Stmt, override val ctx: ContextInfo) : AAInfo {
    override val infoKind: Int get() = 3

    override fun compareInfo(other: AAInfo): Int = compare(other as Unknown)
    fun compare(other: Unknown): Int = stmt.compareTo(other.stmt)
}

data class CallReturn(val stmt: Stmt.Call, override val ctx: ContextInfo) : AAInfo {
    override val infoKind: Int = 1

    override fun compareInfo(other: AAInfo): Int = compare(other as CallReturn)
    fun compare(other: CallReturn): Int = stmt.compareTo(other.stmt)
}

sealed interface LocalAlias : AAInfo {
    data class SimpleLoc(val loc: RefValue) : LocalAlias {
        override val infoKind: Int get() = 2

        override val ctx get() = if (loc is RefValue.Local) loc.ctx else ContextInfo.rootContext

        override fun compareInfo(other: AAInfo): Int = compare(other as SimpleLoc)
        fun compare(other: SimpleLoc): Int = loc.compareTo(other.loc)
    }

    data class Alloc(val stmt: Stmt, override val ctx: ContextInfo) : LocalAlias {
        override val infoKind: Int get() = 0
        override fun compareInfo(other: AAInfo): Int = compare(other as Alloc)
        fun compare(other: Alloc): Int = stmt.compareTo(other.stmt)
    }
}

data class FieldAlias(
    val field: AliasAccessor.Field,
    override val isImmutable: Boolean,
) : AAHeapAccessor {
    override val accessorKind: Int get() = 0
    override fun compareAccessor(accessor: AAHeapAccessor): Int = compare(accessor as FieldAlias)
    fun compare(other: FieldAlias): Int = comparator.compare(this, other)

    companion object {
        private val fieldComparator = compareBy<AliasAccessor.Field> { it.fieldName }
            .thenComparing { it.className }
            .thenComparing { it.fieldType }

        private val comparator = compareBy<FieldAlias> { it.isImmutable }.thenComparing({ it.field }, fieldComparator)
    }
}

data object ArrayAlias : AAHeapAccessor {
    override val isImmutable: Boolean get() = false
    override val accessorKind: Int get() = 1
    override fun compareAccessor(accessor: AAHeapAccessor): Int = 0
}

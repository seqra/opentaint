package org.opentaint.dataflow.ap.ifds.analysis.alias

interface AAInfo : Comparable<AAInfo> {
    val infoKind: Int
    val ctx: ContextInfo

    fun compareInfo(other: AAInfo): Int

    override fun compareTo(other: AAInfo): Int {
        val kindCmp = infoKind.compareTo(other.infoKind)
        if (kindCmp != 0) return kindCmp

        val ctxCmp = ctx.compareTo(other.ctx)
        if (ctxCmp != 0) return ctxCmp

        return compareInfo(other)
    }
}

interface AAHeapAccessor : Comparable<AAHeapAccessor> {
    val isImmutable: Boolean

    val accessorKind: Int

    fun compareAccessor(accessor: AAHeapAccessor): Int

    override fun compareTo(other: AAHeapAccessor): Int {
        val kindCmp = accessorKind.compareTo(other.accessorKind)
        if (kindCmp != 0) return kindCmp
        return compareAccessor(other)
    }
}

data class HeapAlias(
    val instance: Int,
    val heapAccessor: AAHeapAccessor
) : AAInfo {
    override val infoKind: Int get() = 4
    override val ctx get() = ContextInfo.rootContext

    override fun compareInfo(other: AAInfo): Int = compare(other as HeapAlias)

    fun compare(other: HeapAlias): Int {
        val instanceCmp = instance.compareTo(other.instance)
        if (instanceCmp != 0) return instanceCmp
        return heapAccessor.compareTo(other.heapAccessor)
    }
}

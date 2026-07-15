package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import it.unimi.dsi.fastutil.objects.ObjectLinkedOpenHashSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodInitialToFinalBaseOnlyApSummariesStorage(
    methodInitialStatement: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonF2FSummary<BaseOnlyAccess, BaseOnlyAccess>(methodInitialStatement),
    BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
    override fun createStorage(): Storage<BaseOnlyAccess, BaseOnlyAccess> = F2FStorage(apManager)

    private class F2FStorage(private val manager: BaseOnlyApManager) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
        private val perInitial = Long2ObjectOpenHashMap<MergingStorage>()

        override fun add(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val modified = ObjectLinkedOpenHashSet<MergingStorage>()
            for (edge in edges) {
                val ms = perInitial.get(edge.initial) ?: MergingStorage(manager, edge.initial).also { perInitial.put(edge.initial, it) }
                if (ms.add(edge.final, edge.exclusion)) modified += ms
            }
            modified.forEach { it.getAndResetDelta(added) }
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            initialFactPatter: BaseOnlyAccess?,
        ) {
            perInitial.values.forEach { it.collectAll(dst) }
        }
    }

    private class MergingStorage(private val manager: BaseOnlyApManager, private val initial: BaseOnlyAccess) {
        private val finals = Long2ObjectOpenHashMap<ExclusionSet>()
        private val deltaFinals = LongArrayList()
        private val deltaExclusions = ArrayList<ExclusionSet>()

        fun add(final: BaseOnlyAccess, exclusion: ExclusionSet): Boolean {
            if (final.isCollapsed) return false
            val cur = finals[final]
            if (cur == null) {
                finals.put(final, exclusion)
                deltaFinals.add(final)
                deltaExclusions.add(exclusion)
                return true
            }
            val merged = cur.union(exclusion)
            if (merged === cur) return false
            finals.put(final, merged)
            deltaFinals.add(final)
            deltaExclusions.add(merged)
            return true
        }

        fun getAndResetDelta(dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>) {
            for (k in 0 until deltaFinals.size) {
                dst += Builder(manager).setInitialAp(initial).setExitAp(deltaFinals.getLong(k)).setExclusion(deltaExclusions[k])
            }
            deltaFinals.clear()
            deltaExclusions.clear()
        }

        fun collectAll(dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>) {
            finals.forEach { (final, exclusion) ->
                dst += Builder(manager).setInitialAp(initial).setExitAp(final).setExclusion(exclusion)
            }
        }
    }

    private class Builder(override val apManager: BaseOnlyApManager) :
        F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>(), BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
        override fun nonNullIAP(iap: BaseOnlyAccess?): BaseOnlyAccess = iap ?: ABSTRACT_EMPTY_ACCESS
    }
}

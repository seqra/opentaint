package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import it.unimi.dsi.fastutil.longs.LongArrayList
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.util.getOrCreate
import org.opentaint.dataflow.util.getOrCreateNullable
import org.opentaint.dataflow.util.int2ObjectMap
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodInitialToFinalBaseOnlyApSummariesStorage(
    methodInitialStatement: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonF2FSummary<BaseOnlyAccess, BaseOnlyAccess>(methodInitialStatement),
    BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
    override fun createStorage(): Storage<BaseOnlyAccess, BaseOnlyAccess> = F2FStorage(apManager, F2FStorage(apManager, normalizedStorage = null))

    private class F2FStorage(
        private val manager: BaseOnlyApManager,
        private val normalizedStorage: F2FStorage?
    ) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
        private val idEdges = IdEdgeStorage(manager)
        private val perInitial = Long2ObjectOpenHashMap<MergingStorage>()

        override fun add(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val modified = mutableListOf<MergingStorage>()
            for (edge in edges) {
                add(edge.initial, edge.final, edge.exclusion, modified)

                if (normalizedStorage != null) {
                    // The normalized alias lets backward resolution match a concrete stored field via
                    // fieldsCompatible(concreteField, NO_ACCESSOR).
                    val normalizedInitial = normalizeSummaryInitialAccess(edge.initial, edge.final)
                    if (normalizedInitial != edge.initial) {
                        normalizedStorage.add(normalizedInitial, edge.final, edge.exclusion, modified = null)
                    }
                }
            }
            modified.forEach { it.getAndResetDelta(added) }
            idEdges.getAndResetDelta(added)
        }

        private fun add(
            initial: BaseOnlyAccess,
            final: BaseOnlyAccess,
            exclusion: ExclusionSet,
            modified: MutableList<MergingStorage>?,
        ) {
            if (initial == final) {
                idEdges.add(initial, exclusion)
            } else {
                val ms = perInitial.getOrCreate(initial) { MergingStorage(manager, initial) }
                if (ms.add(final, exclusion)) {
                    modified?.add(ms)
                }
            }
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            initialFactPatter: BaseOnlyAccess?,
        ) {
            idEdges.collectAll(dst)
            perInitial.values.forEach { it.collectAll(dst) }

            if (normalizedStorage != null && manager.normalizedEdgesEnabled()) {
                normalizedStorage.collectSummariesTo(dst, initialFactPatter)
            }
        }
    }

    private class IdEdgeStorage(private val manager: BaseOnlyApManager) {
        val storage = StaticLayer()

        fun add(access: BaseOnlyAccess, exclusion: ExclusionSet): Boolean {
            if (access.isCollapsed) return false
            return access.withBaseOnlyAccessUnpacked { s, f, x ->
                storage.add(manager, s, f, x, exclusion)
            }
        }

        fun getAndResetDelta(dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>) {
            storage.getAndResetDelta(manager, dst)
        }

        fun collectAll(dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>) {
            storage.collectAll(manager, dst)
        }
    }

    private abstract class LayerBase<S : Any> {
        var apExclusion: ExclusionSet? = null
        var noAccessor: S? = null
        val concrete = int2ObjectMap<S?>()

        var delta: IntOpenHashSet? = null

        abstract fun createNext(): S

        inline fun add(
            manager: BaseOnlyApManager,
            el: AccessorIdx,
            exclusion: ExclusionSet,
            addNext: S.() -> Boolean,
        ): Boolean {
            if (el == NO_ACCESSOR) {
                val next = noAccessor ?: createNext().also { noAccessor = it }
                return next.addNext()
            }

            if (el == ABSTRACT_MARK) {
                val cur = apExclusion
                val new = cur?.intersect(exclusion) ?: exclusion
                return handleExclusionUpdate(manager, cur, new)
            } else {
                apExclusion?.let { apEx ->
                    val accessorInstance = with(manager) { el.accessor }
                    if (!apEx.contains(accessorInstance)) {
                        return false
                    }
                }

                val next = concrete.getOrCreateNullable(el) { createNext() }
                if (!next.addNext()) return false
                modifiedTracked().add(el)
                return true
            }
        }

        private fun handleExclusionUpdate(manager: BaseOnlyApManager, prev: ExclusionSet?, new: ExclusionSet): Boolean {
            if (prev != null && prev === new) return false

            modifiedTracked().add(ABSTRACT_MARK)
            apExclusion = new

            concrete.keys.toIntArray().forEach { accessorIdx ->
                val accessorInstance = with(manager) { accessorIdx.accessor }
                if (!new.contains(accessorInstance)) {
                    concrete.put(accessorIdx, null)
                }
            }

            return true
        }

        inline fun getAndResetDelta(
            manager: BaseOnlyApManager,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            genAndResetNext: S.(AccessorIdx) -> Unit,
            createThisLevel: () -> BaseOnlyAccess,
        ) {
            noAccessor?.genAndResetNext(NO_ACCESSOR)

            getAndResetModified()?.forEachInt {
                if (it == ABSTRACT_MARK) {
                    apExclusion?.let { ex ->
                        val access = createThisLevel()
                        dst += Builder(manager).setInitialAp(access).setExitAp(access).setExclusion(ex)
                    }
                } else {
                    concrete.get(it)?.genAndResetNext(it)
                }
            }
        }

        fun collectAll(
            manager: BaseOnlyApManager,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            collectNext: S.(AccessorIdx) -> Unit,
            createThisLevel: () -> BaseOnlyAccess,
        ) {
            noAccessor?.collectNext(NO_ACCESSOR)
            apExclusion?.let { ex ->
                val access = createThisLevel()
                dst += Builder(manager).setInitialAp(access).setExitAp(access).setExclusion(ex)
            }

            concrete.forEachEntry { el, next ->
                next?.collectNext(el)
            }
        }

        fun modifiedTracked(): IntOpenHashSet =
            delta ?: IntOpenHashSet().also { delta = it }

        fun getAndResetModified(): IntOpenHashSet? =
            delta?.also { delta = null }
    }

    private class StaticLayer : LayerBase<FieldLayer>() {
        override fun createNext(): FieldLayer = FieldLayer()

        fun add(
            manager: BaseOnlyApManager,
            s: AccessorIdx,
            f: AccessorIdx,
            x: AccessorIdx,
            exclusion: ExclusionSet
        ): Boolean =
            add(manager, s, exclusion) { add(manager, f, x, exclusion) }

        fun getAndResetDelta(
            manager: BaseOnlyApManager,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>
        ) = getAndResetDelta(
            manager, dst,
            { getAndResetDelta(manager, it, dst) },
            { packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR) }
        )

        fun collectAll(
            manager: BaseOnlyApManager,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>
        ) = collectAll(
            manager, dst,
            { collectAll(manager, it, dst) },
            { packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR) }
        )
    }

    private class FieldLayer : LayerBase<SuffixLayer>() {
        override fun createNext(): SuffixLayer = SuffixLayer()

        fun add(manager: BaseOnlyApManager, f: AccessorIdx, x: AccessorIdx, exclusion: ExclusionSet): Boolean =
            add(manager, f, exclusion) { add(manager, x, exclusion) }

        fun getAndResetDelta(
            manager: BaseOnlyApManager,
            s: AccessorIdx,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>
        ) = getAndResetDelta(
            manager, dst,
            { getAndResetDelta(manager, s, it, dst) },
            { packBaseOnlyAccess(s, ABSTRACT_MARK, NO_ACCESSOR) }
        )

        fun collectAll(
            manager: BaseOnlyApManager,
            s: AccessorIdx,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>
        ) = collectAll(
            manager, dst,
            { collectAll(manager, s, it, dst) },
            { packBaseOnlyAccess(s, ABSTRACT_MARK, NO_ACCESSOR) }
        )
    }

    private class SuffixLayer : LayerBase<SuffixLayer.MutableExclusion>() {
        private class MutableExclusion(var ex: ExclusionSet)

        override fun createNext(): MutableExclusion = MutableExclusion(ExclusionSet.Universe)

        fun add(manager: BaseOnlyApManager, x: AccessorIdx, exclusion: ExclusionSet): Boolean =
            add(manager, x, exclusion) {
                val cur = ex
                val intersection = cur.intersect(exclusion)
                ex = intersection
                intersection !== cur
            }

        fun getAndResetDelta(
            manager: BaseOnlyApManager,
            s: AccessorIdx,
            f: AccessorIdx,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>
        ) = getAndResetDelta(
            manager, dst,
            {
                val access = packBaseOnlyAccess(s, f, it)
                dst += Builder(manager).setInitialAp(access).setExitAp(access).setExclusion(ex)
            },
            { packBaseOnlyAccess(s, f, ABSTRACT_MARK) }
        )

        fun collectAll(
            manager: BaseOnlyApManager,
            s: AccessorIdx,
            f: AccessorIdx,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>
        ) = collectAll(
            manager, dst,
            {
                val access = packBaseOnlyAccess(s, f, it)
                dst += Builder(manager).setInitialAp(access).setExitAp(access).setExclusion(ex)
            },
            { packBaseOnlyAccess(s, f, ABSTRACT_MARK) }
        )
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
                dst += Builder(manager).setInitialAp(initial).setExitAp(deltaFinals.getLong(k))
                    .setExclusion(deltaExclusions[k])
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

internal fun normalizeSummaryInitialAccess(initial: BaseOnlyAccess, final: BaseOnlyAccess): BaseOnlyAccess {
    if (initial.apSlot != 1 || final.apSlot != 2) return initial
    return packBaseOnlyAccess(initial.staticIdx, NO_ACCESSOR, ABSTRACT_MARK)
}

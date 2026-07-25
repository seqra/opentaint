package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.longs.LongArrayList
import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSummary
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.util.forEachEntry
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.util.forEachLong
import org.opentaint.dataflow.util.getOrCreateNullable
import org.opentaint.dataflow.util.int2ObjectMap
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodInitialToFinalBaseOnlyApSummariesStorage(
    methodInitialStatement: CommonInst,
    override val apManager: BaseOnlyApManager,
) : CommonF2FSummary<BaseOnlyAccess, BaseOnlyAccess>(methodInitialStatement),
    BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
    override fun createStorage(): Storage<BaseOnlyAccess, BaseOnlyAccess> = F2FStorage(apManager)

    private class F2FStorage(
        private val manager: BaseOnlyApManager,
    ) : Storage<BaseOnlyAccess, BaseOnlyAccess> {
        private val idEdges = IdEdgeStorage(manager)
        private val perInitial = BaseOnlyInitialAccessIndex<MergingStorage>()

        override fun add(
            edges: List<StorageEdge<BaseOnlyAccess, BaseOnlyAccess>>,
            added: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val modified = linkedSetOf<MergingStorage>()
            for (edge in edges) {
                if (edge.initial.isCollapsed || edge.final.isCollapsed) continue
                if (edge.initial == edge.final) {
                    idEdges.add(edge.initial, edge.exclusion)
                } else {
                    val storage = perInitial.getOrCreate(edge.initial) { MergingStorage(manager, edge.initial) }
                    if (storage.add(edge.final, edge.exclusion)) modified += storage
                }
            }

            modified.forEach { it.getAndResetDelta(added) }
            idEdges.getAndResetDelta(added)
        }

        override fun collectSummariesTo(
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            initialFactPatter: BaseOnlyAccess?,
        ) {
            val normalizedEnabled = manager.normalizedEdgesEnabled()
            val emit: (BaseOnlyAccess, BaseOnlyAccess, ExclusionSet) -> Unit = { initial, final, exclusion ->
                dst += Builder(manager).setInitialAp(initial).setExitAp(final).setExclusion(exclusion)
            }

            if (!normalizedEnabled) {
                collectSummaries(initialFactPatter, emit)
                return
            }

            val views = linkedMapOf<SummaryKey, ExclusionSet>()
            fun addView(initial: BaseOnlyAccess, final: BaseOnlyAccess, exclusion: ExclusionSet) {
                val key = SummaryKey(initial, final)
                views[key] = views[key]?.intersect(exclusion) ?: exclusion
            }

            // A normalized initial is a read-only view of its primary edge.  It owns no
            // exclusion state and emits no delta.  Scan primaries in trace mode because an
            // alias can match a pattern that does not select the primary initial itself.
            collectSummaries(null) { initial, final, exclusion ->
                addView(initial, final, exclusion)
                val normalized = normalizeSummaryInitialAccess(initial, final)
                if (normalized != initial) {
                    addView(normalized, final, exclusion)
                }
            }
            views.forEach { (key, exclusion) -> emit(key.initial, key.final, exclusion) }
        }

        private fun collectSummaries(
            initialFactPattern: BaseOnlyAccess?,
            emit: (BaseOnlyAccess, BaseOnlyAccess, ExclusionSet) -> Unit,
        ) {
            if (initialFactPattern == null) {
                idEdges.collectAll(emit)
                perInitial.collectAll { _, storage -> storage.collectAll(emit) }
            } else {
                idEdges.collectContainedBy(initialFactPattern, emit)
                perInitial.collectCandidates(initialFactPattern) { initial, storage ->
                    if (baseOnlySummaryInitialMatches(initialFactPattern, initial)) storage.collectAll(emit)
                }
            }
        }
    }

    private data class SummaryKey(
        val initial: BaseOnlyAccess,
        val final: BaseOnlyAccess,
    )

    private class IdEdgeStorage(private val manager: BaseOnlyApManager) {
        private val storage = StaticLayer()

        fun add(access: BaseOnlyAccess, exclusion: ExclusionSet): Boolean {
            if (access.isCollapsed) return false
            return access.withBaseOnlyAccessUnpacked { staticIdx, fieldIdx, suffixIdx ->
                storage.add(manager, staticIdx, fieldIdx, suffixIdx, access.rawSuffixSlot, exclusion)
            }
        }

        fun getAndResetDelta(dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>) {
            storage.getAndResetDelta(manager, dst)
        }

        fun collectAll(emit: (BaseOnlyAccess, BaseOnlyAccess, ExclusionSet) -> Unit) {
            storage.collectAll { access, exclusion -> emit(access, access, exclusion) }
        }

        fun collectContainedBy(
            pattern: BaseOnlyAccess,
            emit: (BaseOnlyAccess, BaseOnlyAccess, ExclusionSet) -> Unit,
        ) {
            storage.collectContainedBy(pattern) { access, exclusion -> emit(access, access, exclusion) }
        }
    }

    private abstract class LayerBase<S : Any> {
        var apExclusion: ExclusionSet? = null
        var noAccessor: S? = null
        val concrete = int2ObjectMap<S?>()
        private var delta: IntOpenHashSet? = null

        abstract fun createNext(): S

        inline fun add(
            manager: BaseOnlyApManager,
            accessorIdx: AccessorIdx,
            exclusion: ExclusionSet,
            addNext: S.() -> Boolean,
        ): Boolean {
            if (accessorIdx == NO_ACCESSOR) {
                val next = noAccessor ?: createNext().also { noAccessor = it }
                return next.addNext()
            }

            if (accessorIdx == ABSTRACT_MARK) {
                val current = apExclusion
                val merged = current?.intersect(exclusion) ?: exclusion
                return updateAbstraction(manager, current, merged)
            }

            apExclusion?.let { abstractExclusion ->
                val accessor = with(manager) { accessorIdx.accessor }
                if (!abstractExclusion.contains(accessor)) return false
            }

            val next = concrete.getOrCreateNullable(accessorIdx) { createNext() }
            if (!next.addNext()) return false
            modified().add(accessorIdx)
            return true
        }

        private fun updateAbstraction(
            manager: BaseOnlyApManager,
            current: ExclusionSet?,
            merged: ExclusionSet,
        ): Boolean {
            if (current != null && current === merged) return false

            modified().add(ABSTRACT_MARK)
            apExclusion = merged
            concrete.keys.toIntArray().forEach { accessorIdx ->
                val accessor = with(manager) { accessorIdx.accessor }
                if (!merged.contains(accessor)) concrete.put(accessorIdx, null)
            }
            return true
        }

        inline fun getAndResetDelta(
            manager: BaseOnlyApManager,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
            emitNext: S.(AccessorIdx) -> Unit,
            createAbstraction: () -> BaseOnlyAccess,
        ) {
            noAccessor?.emitNext(NO_ACCESSOR)
            getAndResetModified()?.forEachInt { accessorIdx ->
                if (accessorIdx == ABSTRACT_MARK) {
                    apExclusion?.let { exclusion ->
                        val access = createAbstraction()
                        dst += Builder(manager).setInitialAp(access).setExitAp(access).setExclusion(exclusion)
                    }
                } else {
                    concrete.get(accessorIdx)?.emitNext(accessorIdx)
                }
            }
        }

        fun collectAll(
            collectNext: S.(AccessorIdx) -> Unit,
            createAbstraction: () -> BaseOnlyAccess,
            emit: (BaseOnlyAccess, ExclusionSet) -> Unit,
        ) {
            noAccessor?.collectNext(NO_ACCESSOR)
            apExclusion?.let { emit(createAbstraction(), it) }
            concrete.forEachEntry { accessorIdx, next -> next?.collectNext(accessorIdx) }
        }

        private fun modified(): IntOpenHashSet = delta ?: IntOpenHashSet().also { delta = it }

        private fun getAndResetModified(): IntOpenHashSet? = delta?.also { delta = null }
    }

    private class StaticLayer : LayerBase<FieldLayer>() {
        override fun createNext(): FieldLayer = FieldLayer()

        fun add(
            manager: BaseOnlyApManager,
            staticIdx: AccessorIdx,
            fieldIdx: AccessorIdx,
            suffixIdx: AccessorIdx,
            rawSuffixSlot: Int,
            exclusion: ExclusionSet,
        ): Boolean = add(manager, staticIdx, exclusion) {
            add(manager, fieldIdx, suffixIdx, rawSuffixSlot, exclusion)
        }

        fun getAndResetDelta(
            manager: BaseOnlyApManager,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) = getAndResetDelta(
            manager,
            dst,
            { getAndResetDelta(manager, it, dst) },
            { packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR) },
        )

        fun collectAll(emit: (BaseOnlyAccess, ExclusionSet) -> Unit) = collectAll(
            { collectAll(it, emit) },
            { packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR) },
            emit,
        )

        fun collectContainedBy(pattern: BaseOnlyAccess, emit: (BaseOnlyAccess, ExclusionSet) -> Unit) {
            if (pattern.staticIdx == ABSTRACT_MARK) {
                collectAll(emit)
                return
            }

            apExclusion?.let { exclusion ->
                emitIfApplicable(packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR), exclusion, pattern, emit)
            }
            val next = if (pattern.staticIdx == NO_ACCESSOR) noAccessor else concrete.get(pattern.staticIdx)
            next?.collectContainedBy(pattern.staticIdx, pattern, emit)
        }
    }

    private class FieldLayer : LayerBase<SuffixLayer>() {
        override fun createNext(): SuffixLayer = SuffixLayer()

        fun add(
            manager: BaseOnlyApManager,
            fieldIdx: AccessorIdx,
            suffixIdx: AccessorIdx,
            rawSuffixSlot: Int,
            exclusion: ExclusionSet,
        ): Boolean = add(manager, fieldIdx, exclusion) {
            add(manager, suffixIdx, rawSuffixSlot, exclusion)
        }

        fun getAndResetDelta(
            manager: BaseOnlyApManager,
            staticIdx: AccessorIdx,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) = getAndResetDelta(
            manager,
            dst,
            { getAndResetDelta(manager, staticIdx, it, dst) },
            { packBaseOnlyAccess(staticIdx, ABSTRACT_MARK, NO_ACCESSOR) },
        )

        fun collectAll(staticIdx: AccessorIdx, emit: (BaseOnlyAccess, ExclusionSet) -> Unit) = collectAll(
            { collectAll(staticIdx, it, emit) },
            { packBaseOnlyAccess(staticIdx, ABSTRACT_MARK, NO_ACCESSOR) },
            emit,
        )

        fun collectContainedBy(
            staticIdx: AccessorIdx,
            pattern: BaseOnlyAccess,
            emit: (BaseOnlyAccess, ExclusionSet) -> Unit,
        ) {
            if (pattern.fieldIdx == ABSTRACT_MARK) {
                collectAll(staticIdx, emit)
                return
            }

            apExclusion?.let { exclusion ->
                emitIfApplicable(packBaseOnlyAccess(staticIdx, ABSTRACT_MARK, NO_ACCESSOR), exclusion, pattern, emit)
            }
            if (pattern.fieldIdx == NO_ACCESSOR) {
                noAccessor?.collectContainedBy(staticIdx, NO_ACCESSOR, pattern, emit)
                concrete.forEachEntry { fieldIdx, next ->
                    next?.collectContainedBy(staticIdx, fieldIdx, pattern, emit)
                }
                return
            }

            noAccessor?.collectContainedBy(staticIdx, NO_ACCESSOR, pattern, emit)
            concrete.get(pattern.fieldIdx)?.collectContainedBy(staticIdx, pattern.fieldIdx, pattern, emit)
        }
    }

    private class SuffixLayer {
        private class MutableExclusion(@Volatile var exclusion: ExclusionSet)

        private var apExclusion: ExclusionSet? = null
        private var noAccessor: MutableExclusion? = null
        private val concrete = int2ObjectMap<MutableExclusion?>()
        private var delta: IntOpenHashSet? = null

        fun add(
            manager: BaseOnlyApManager,
            suffixIdx: AccessorIdx,
            rawSuffixSlot: Int,
            exclusion: ExclusionSet,
        ): Boolean {
            if (suffixIdx == NO_ACCESSOR) {
                val current = noAccessor
                if (current == null) {
                    noAccessor = MutableExclusion(exclusion)
                    modified().add(NO_ACCESSOR)
                    return true
                }
                return current.intersect(exclusion).also { if (it) modified().add(NO_ACCESSOR) }
            }

            if (suffixIdx == ABSTRACT_MARK) {
                val current = apExclusion
                val merged = current?.intersect(exclusion) ?: exclusion
                if (current != null && current === merged) return false
                modified().add(ABSTRACT_MARK)
                apExclusion = merged
                concrete.keys.toIntArray().forEach { rawSlot ->
                    val concreteSuffix = suffixIdxFromRawSlot(rawSlot)
                    val accessor = with(manager) { concreteSuffix.accessor }
                    if (!merged.contains(accessor)) concrete.put(rawSlot, null)
                }
                return true
            }

            apExclusion?.let { abstractExclusion ->
                val accessor = with(manager) { suffixIdx.accessor }
                if (!abstractExclusion.contains(accessor)) return false
            }

            val current = concrete.get(rawSuffixSlot)
            if (current == null) {
                concrete.put(rawSuffixSlot, MutableExclusion(exclusion))
                modified().add(rawSuffixSlot)
                return true
            }
            return current.intersect(exclusion).also { if (it) modified().add(rawSuffixSlot) }
        }

        fun getAndResetDelta(
            manager: BaseOnlyApManager,
            staticIdx: AccessorIdx,
            fieldIdx: AccessorIdx,
            dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>,
        ) {
            val modified = delta?.also { delta = null } ?: return
            modified.forEachInt { key ->
                val accessAndExclusion = when (key) {
                    NO_ACCESSOR -> packBaseOnlyAccess(staticIdx, fieldIdx, NO_ACCESSOR) to noAccessor?.exclusion
                    ABSTRACT_MARK -> packBaseOnlyAccess(staticIdx, fieldIdx, ABSTRACT_MARK) to apExclusion
                    else -> packBaseOnlyAccessFromRawSuffix(staticIdx, fieldIdx, key) to concrete.get(key)?.exclusion
                }
                val exclusion = accessAndExclusion.second ?: return@forEachInt
                val access = accessAndExclusion.first
                dst += Builder(manager).setInitialAp(access).setExitAp(access).setExclusion(exclusion)
            }
        }

        fun collectAll(
            staticIdx: AccessorIdx,
            fieldIdx: AccessorIdx,
            emit: (BaseOnlyAccess, ExclusionSet) -> Unit,
        ) {
            noAccessor?.let { emit(packBaseOnlyAccess(staticIdx, fieldIdx, NO_ACCESSOR), it.exclusion) }
            apExclusion?.let { emit(packBaseOnlyAccess(staticIdx, fieldIdx, ABSTRACT_MARK), it) }
            concrete.forEachEntry { rawSlot, entry ->
                entry?.let { emit(packBaseOnlyAccessFromRawSuffix(staticIdx, fieldIdx, rawSlot), it.exclusion) }
            }
        }

        fun collectContainedBy(
            staticIdx: AccessorIdx,
            fieldIdx: AccessorIdx,
            pattern: BaseOnlyAccess,
            emit: (BaseOnlyAccess, ExclusionSet) -> Unit,
        ) {
            if (pattern.suffixIdx == ABSTRACT_MARK) {
                collectAll(staticIdx, fieldIdx, emit)
                return
            }

            apExclusion?.let { exclusion ->
                emitIfApplicable(packBaseOnlyAccess(staticIdx, fieldIdx, ABSTRACT_MARK), exclusion, pattern, emit)
            }
            if (pattern.suffixIdx == NO_ACCESSOR) {
                noAccessor?.let {
                    emitIfApplicable(packBaseOnlyAccess(staticIdx, fieldIdx, NO_ACCESSOR), it.exclusion, pattern, emit)
                }
                return
            }

            val states = if (pattern.hasSemanticMark) {
                BaseOnlyValueAccessorState.entries
            } else {
                listOf(BaseOnlyValueAccessorState.Normal)
            }
            for (state in states) {
                val rawSlot = rawBaseOnlySuffixSlot(pattern.suffixIdx, state)
                val entry = concrete.get(rawSlot) ?: continue
                emitIfApplicable(packBaseOnlyAccessFromRawSuffix(staticIdx, fieldIdx, rawSlot), entry.exclusion, pattern, emit)
            }
        }

        private fun MutableExclusion.intersect(exclusion: ExclusionSet): Boolean {
            val current = this.exclusion
            val merged = current.intersect(exclusion)
            if (merged === current) return false
            this.exclusion = merged
            return true
        }

        private fun modified(): IntOpenHashSet = delta ?: IntOpenHashSet().also { delta = it }

        private fun suffixIdxFromRawSlot(rawSlot: Int): AccessorIdx =
            (rawSlot and BASE_ONLY_SUFFIX_VALUE_MASK) - BASE_ONLY_BIAS
    }

    private class MergingStorage(
        private val manager: BaseOnlyApManager,
        private val initial: BaseOnlyAccess,
    ) {
        private val finals = org.opentaint.dataflow.util.longSet()
        private val deltaFinals = LongOpenHashSet()

        @Volatile
        private var aggregateExclusion: ExclusionSet? = null

        fun add(final: BaseOnlyAccess, exclusion: ExclusionSet): Boolean {
            if (final.isCollapsed) return false
            val currentExclusion = aggregateExclusion
            val mergedExclusion = currentExclusion?.union(exclusion) ?: exclusion
            val exclusionChanged = currentExclusion == null || mergedExclusion !== currentExclusion

            // The exclusion aggregate is initialized before a new final is published.
            aggregateExclusion = mergedExclusion
            val finalAdded = finals.add(final)
            if (exclusionChanged) {
                finals.forEachLong(deltaFinals::add)
            } else if (finalAdded) {
                deltaFinals.add(final)
            }
            return exclusionChanged || finalAdded
        }

        fun getAndResetDelta(dst: MutableList<F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>>) {
            val exclusion = aggregateExclusion ?: return
            val iterator = deltaFinals.iterator()
            while (iterator.hasNext()) {
                val final = iterator.nextLong()
                dst += Builder(manager).setInitialAp(initial).setExitAp(final)
                    .setExclusion(exclusion)
            }
            deltaFinals.clear()
        }

        fun collectAll(emit: (BaseOnlyAccess, BaseOnlyAccess, ExclusionSet) -> Unit) {
            // The writer publishes the aggregate exclusion before a new final. Snapshot finals
            // first and read the volatile exclusion afterwards, so a reader that observes a new
            // final cannot pair it with the older aggregate exclusion.
            val snapshot = LongArrayList()
            finals.forEachLong(snapshot::add)
            val exclusion = aggregateExclusion ?: return
            for (index in 0 until snapshot.size) {
                emit(initial, snapshot.getLong(index), exclusion)
            }
        }
    }

    private class Builder(override val apManager: BaseOnlyApManager) :
        F2FBBuilder<BaseOnlyAccess, BaseOnlyAccess>(), BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {
        override fun nonNullIAP(iap: BaseOnlyAccess?): BaseOnlyAccess = iap ?: ABSTRACT_EMPTY_ACCESS
    }
}

private fun emitIfApplicable(
    access: BaseOnlyAccess,
    exclusion: ExclusionSet,
    pattern: BaseOnlyAccess,
    emit: (BaseOnlyAccess, ExclusionSet) -> Unit,
) {
    if (baseOnlySummaryInitialMatches(pattern, access)) emit(access, exclusion)
}

internal fun normalizeSummaryInitialAccess(initial: BaseOnlyAccess, final: BaseOnlyAccess): BaseOnlyAccess {
    if (initial.apSlot != 1 || final.apSlot != 2) return initial
    return packBaseOnlyAccess(initial.staticIdx, NO_ACCESSOR, ABSTRACT_MARK)
}

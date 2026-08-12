package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.LongArrayList
import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import it.unimi.dsi.fastutil.longs.LongOpenHashSet
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.LanguageManager
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageIdx
import org.opentaint.dataflow.ap.ifds.MethodAnalyzerEdges.Companion.instructionStorageSize
import org.opentaint.dataflow.ap.ifds.access.common.CommonF2FSet
import org.opentaint.ir.api.common.cfg.CommonInst

class MethodEdgesInitialToFinalBaseOnlyApSet(
    methodInitialStatement: CommonInst,
    private val maxInstIdx: Int,
    private val languageManager: LanguageManager,
    override val apManager: BaseOnlyApManager,
) : CommonF2FSet<BaseOnlyAccess, BaseOnlyAccess>(methodInitialStatement),
    BaseOnlyInitialApAccess, BaseOnlyFinalApAccess {

    override fun mostAbstractPattern(base: AccessPathBase): BaseOnlyAccess = ABSTRACT_EMPTY_ACCESS

    override fun createApStorage(): ApStorage<BaseOnlyAccess, BaseOnlyAccess> = Storage()

    private inner class Storage : ApStorage<BaseOnlyAccess, BaseOnlyAccess> {
        private val statements = arrayOfNulls<StatementState>(instructionStorageSize(maxInstIdx))

        override fun add(
            statement: CommonInst,
            initial: BaseOnlyAccess,
            final: AccessWithExclusion<BaseOnlyAccess>,
        ): List<AccessWithExclusion<BaseOnlyAccess>> {
            if (initial.isCollapsed || final.access.isCollapsed) return emptyList()
            return statementState(statement, create = true)!!.add(initial, final)
        }

        override fun filter(
            dst: MutableList<Pair<BaseOnlyAccess, AccessWithExclusion<BaseOnlyAccess>>>,
            statement: CommonInst,
            finalPattern: BaseOnlyAccess,
        ) {
            statementState(statement, create = false)?.collect(finalPattern) { initial, final ->
                dst.add(initial to final)
            }

            traceGeneralizationAt(statement)?.let { edge ->
                val generalized = edge.initial to AccessWithExclusion(edge.final, edge.exclusion)
                dst += generalized
            }
        }

        override fun filter(
            dst: MutableList<AccessWithExclusion<BaseOnlyAccess>>,
            statement: CommonInst,
            initial: BaseOnlyAccess,
            finalPattern: BaseOnlyAccess,
        ) {
            statementState(statement, create = false)?.collect(initial, finalPattern) { dst.add(it) }

            if (!apManager.traceResolutionModeEnabled()) return

            // Trace-time summary normalization exposes a field-abstract initial as a
            // suffix-abstract alias. Resolve that view back to the primary intraprocedural
            // key; the alias itself is never stored.
            if (initial.apSlot == 2 && finalPattern.apSlot == 2) {
                val primary = packBaseOnlyAccess(initial.staticIdx, ABSTRACT_MARK, NO_ACCESSOR)
                statementState(statement, create = false)?.collect(primary, finalPattern) { dst.addDistinct(it) }
            }

            traceGeneralizationAt(statement)
                ?.takeIf { baseOnlySummaryInitialMatches(initial, it.initial) }
                ?.let { dst.addDistinct(AccessWithExclusion(it.final, it.exclusion)) }
        }

        private fun traceGeneralizationAt(statement: CommonInst): BaseOnlySummaryEdge? {
            if (!apManager.traceResolutionModeEnabled() || !apManager.fieldGeneralizationEnabled) return null

            val exact = arrayListOf<BaseOnlySummaryEdge>()
            statementState(statement, create = false)?.collect(finalPattern = null) { initial, final ->
                exact += BaseOnlySummaryEdge(initial, final.access, final.exclusion)
            }
            if (exact.isEmpty()) return null

            val generalizer = BaseOnlyF2FFieldGeneralizer(maxEnumeratedEdges = 0)
            val result = generalizer.rewrite(exact)
            val group = result.newlyGeneralized.singleOrNull() ?: return null
            return generalizer.representative(group)
        }

        private fun statementState(statement: CommonInst, create: Boolean): StatementState? {
            val idx = instructionStorageIdx(statement, languageManager)
            val current = statements[idx]
            if (current != null || !create) return current
            return StatementState().also { statements[idx] = it }
        }
    }

    private class StatementState {
        private val initials = Long2ObjectOpenHashMap<InitialState>()
        private val conclusions = BaseOnlyInitialAccessIndex<InitialSupport>()

        fun add(
            initial: BaseOnlyAccess,
            final: AccessWithExclusion<BaseOnlyAccess>,
        ): List<AccessWithExclusion<BaseOnlyAccess>> {
            val state = initials[initial]
            if (state == null) {
                initials.put(initial, InitialState(final))
                conclusion(final.access).add(initial)
                return listOf(final)
            }

            val update = state.add(final)
            if (!update.changed) return emptyList()
            update.removedFinals.forEach { removed ->
                conclusions.get(removed)?.remove(initial)
            }
            if (update.finalAdded) conclusion(final.access).add(initial)
            return update.delta
        }

        fun collect(
            finalPattern: BaseOnlyAccess?,
            out: (BaseOnlyAccess, AccessWithExclusion<BaseOnlyAccess>) -> Unit,
        ) {
            val collectSupport: (BaseOnlyAccess, InitialSupport) -> Unit = collectSupport@{ final, support ->
                if (support.isEmpty ||
                    finalPattern != null && !baseOnlySummaryInitialMatches(finalPattern, final)
                ) return@collectSupport
                support.forEach { initial ->
                    val state = initials[initial] ?: error("Missing initial support")
                    out(initial, AccessWithExclusion(final, state.exclusion))
                }
            }
            if (finalPattern == null) {
                conclusions.collectAll(collectSupport)
            } else {
                conclusions.collectCandidates(finalPattern, collectSupport)
            }
        }

        fun collect(
            initial: BaseOnlyAccess,
            finalPattern: BaseOnlyAccess,
            out: (AccessWithExclusion<BaseOnlyAccess>) -> Unit,
        ) {
            initials[initial]?.collect(finalPattern, out)
        }

        private fun conclusion(final: BaseOnlyAccess): InitialSupport =
            conclusions.getOrCreate(final, ::InitialSupport)
    }

    private class InitialState(first: AccessWithExclusion<BaseOnlyAccess>) {
        private var firstFinal = first.access
        private var multipleFinals: LongOpenHashSet? = null
        var exclusion: ExclusionSet = first.exclusion
            private set

        fun add(final: AccessWithExclusion<BaseOnlyAccess>): InitialUpdate {
            val accessUpdate = addAccess(final.access)
            val mergedExclusion = exclusion.union(final.exclusion)
            val exclusionChanged = mergedExclusion != exclusion
            if (!accessUpdate.changed && !exclusionChanged) return InitialUpdate.Unchanged

            exclusion = mergedExclusion
            val delta = if (exclusionChanged) {
                buildList { collect(finalPattern = null) { add(it) } }
            } else {
                listOf(AccessWithExclusion(final.access, exclusion))
            }
            return InitialUpdate(
                changed = true,
                finalAdded = accessUpdate.changed,
                removedFinals = accessUpdate.removed,
                delta = delta,
            )
        }

        fun collect(
            finalPattern: BaseOnlyAccess?,
            out: (AccessWithExclusion<BaseOnlyAccess>) -> Unit,
        ) {
            val finals = multipleFinals
            if (finals == null) {
                if (finalPattern == null || baseOnlySummaryInitialMatches(finalPattern, firstFinal)) {
                    out(AccessWithExclusion(firstFinal, exclusion))
                }
                return
            }
            finals.forEach { access ->
                if (finalPattern == null || baseOnlySummaryInitialMatches(finalPattern, access)) {
                    out(AccessWithExclusion(access, exclusion))
                }
            }
        }

        private fun addAccess(access: BaseOnlyAccess): AccessUpdate {
            val finals = multipleFinals
            if (finals != null) {
                if (finals.containsCoverOf(access)) return AccessUpdate.Unchanged

                val removed = LongArrayList()
                if (access.mayCoverDistinctAccess()) {
                    val covered = finals.iterator()
                    while (covered.hasNext()) {
                        val candidate = covered.nextLong()
                        if (BaseOnlyAccessOps.covers(access, candidate)) {
                            covered.remove()
                            removed.add(candidate)
                        }
                    }
                }

                val added = finals.add(access)
                if (!added) return AccessUpdate.Unchanged
                if (finals.size == 1) {
                    firstFinal = access
                    multipleFinals = null
                }
                return AccessUpdate(true, removed)
            }
            if (BaseOnlyAccessOps.covers(firstFinal, access)) return AccessUpdate.Unchanged
            if (BaseOnlyAccessOps.covers(access, firstFinal)) {
                val removed = LongArrayList(1).also { it.add(firstFinal) }
                firstFinal = access
                return AccessUpdate(true, removed)
            }

            multipleFinals = LongOpenHashSet(2).also {
                it.add(firstFinal)
                it.add(access)
            }
            return AccessUpdate(true, LongArrayList())
        }
    }

    private class InitialSupport {
        private var first: BaseOnlyAccess = NO_SUPPORT
        private var multiple: LongOpenHashSet? = null

        val isEmpty: Boolean get() = first == NO_SUPPORT

        fun add(initial: BaseOnlyAccess) {
            val supports = multiple
            if (supports != null) {
                supports.add(initial)
                return
            }
            if (first == NO_SUPPORT) {
                first = initial
            } else if (first != initial) {
                multiple = LongOpenHashSet(2).also {
                    it.add(first)
                    it.add(initial)
                }
            }
        }

        fun remove(initial: BaseOnlyAccess) {
            val supports = multiple
            if (supports == null) {
                if (first == initial) first = NO_SUPPORT
                return
            }
            if (!supports.remove(initial)) return
            if (supports.size == 1) {
                first = supports.iterator().nextLong()
                multiple = null
            }
        }

        fun forEach(action: (BaseOnlyAccess) -> Unit) {
            multiple?.forEach(action) ?: first.takeUnless { it == NO_SUPPORT }?.let(action)
        }
    }

    private data class InitialUpdate(
        val changed: Boolean,
        val finalAdded: Boolean,
        val removedFinals: LongArrayList,
        val delta: List<AccessWithExclusion<BaseOnlyAccess>>,
    ) {
        companion object {
            val Unchanged = InitialUpdate(false, false, LongArrayList(), emptyList())
        }
    }

    private data class AccessUpdate(
        val changed: Boolean,
        val removed: LongArrayList,
    ) {
        companion object {
            val Unchanged = AccessUpdate(false, LongArrayList())
        }
    }

    private fun MutableList<AccessWithExclusion<BaseOnlyAccess>>.addDistinct(
        value: AccessWithExclusion<BaseOnlyAccess>,
    ) {
        if (value !in this) add(value)
    }

    private companion object {
        const val NO_SUPPORT: BaseOnlyAccess = Long.MIN_VALUE
    }
}

private fun LongOpenHashSet.containsCoverOf(access: BaseOnlyAccess): Boolean {
    if (contains(access)) return true
    if (contains(packBaseOnlyAccess(ABSTRACT_MARK, NO_ACCESSOR, NO_ACCESSOR))) return true
    if (access.staticIdx == ABSTRACT_MARK) return false

    if (contains(packBaseOnlyAccess(access.staticIdx, ABSTRACT_MARK, NO_ACCESSOR))) return true
    if (access.fieldIdx == ABSTRACT_MARK) return false

    if (contains(packBaseOnlyAccess(access.staticIdx, access.fieldIdx, ABSTRACT_MARK))) return true
    if (access.fieldIdx < 0) return false

    if (contains(packBaseOnlyAccess(access.staticIdx, NO_ACCESSOR, ABSTRACT_MARK))) return true
    if (!access.hasSemanticMark) return false

    return contains(
        packBaseOnlyAccess(
            access.staticIdx,
            NO_ACCESSOR,
            access.suffixIdx,
            access.valueAccessorState,
        )
    )
}

private fun BaseOnlyAccess.mayCoverDistinctAccess(): Boolean =
    staticIdx == ABSTRACT_MARK ||
        fieldIdx == ABSTRACT_MARK ||
        suffixIdx == ABSTRACT_MARK ||
        (fieldIdx == NO_ACCESSOR && hasSemanticMark)

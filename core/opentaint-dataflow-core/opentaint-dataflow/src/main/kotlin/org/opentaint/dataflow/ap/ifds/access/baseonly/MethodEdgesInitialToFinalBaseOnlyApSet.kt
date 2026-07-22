package org.opentaint.dataflow.ap.ifds.access.baseonly

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
        private val perInitial = Long2ObjectOpenHashMap<PerStatement>()

        override fun add(
            statement: CommonInst,
            initial: BaseOnlyAccess,
            final: AccessWithExclusion<BaseOnlyAccess>,
        ): List<AccessWithExclusion<BaseOnlyAccess>> {
            if (initial.isCollapsed || final.access.isCollapsed) return emptyList()
            val ps = perInitial.get(initial)
                ?: PerStatement(maxInstIdx, languageManager).also { perInitial.put(initial, it) }
            return ps.add(statement, final)
        }

        override fun filter(
            dst: MutableList<Pair<BaseOnlyAccess, AccessWithExclusion<BaseOnlyAccess>>>,
            statement: CommonInst,
            finalPattern: BaseOnlyAccess,
        ) {
            perInitial.forEach { (initial, ps) -> ps.collectAt(statement) { dst.add(initial to it) } }
        }

        override fun filter(
            dst: MutableList<AccessWithExclusion<BaseOnlyAccess>>,
            statement: CommonInst,
            initial: BaseOnlyAccess,
            finalPattern: BaseOnlyAccess,
        ) {
            perInitial[initial]?.collectAt(statement) { dst.add(it) }

            if (apManager.normalizedEdgesEnabled()) {
                // Trace-time summary normalization exposes a field-abstract initial as a
                // suffix-abstract alias. Resolve that view back to the primary intraprocedural
                // key; the alias itself is never stored.
                if (initial.apSlot != 2 || finalPattern.apSlot != 2) return
                val primary = packBaseOnlyAccess(initial.staticIdx, ABSTRACT_MARK, NO_ACCESSOR)
                perInitial[primary]?.collectAt(statement) { dst.add(it) }
            }
        }
    }

    private class PerStatement(
        maxInstIdx: Int,
        private val languageManager: LanguageManager,
    ) {
        private val entries = arrayOfNulls<Entry>(instructionStorageSize(maxInstIdx))

        private class Entry(first: AccessWithExclusion<BaseOnlyAccess>) {
            private val finals = LongOpenHashSet().also { it.add(first.access) }
            private var exclusion: ExclusionSet = first.exclusion

            fun add(final: AccessWithExclusion<BaseOnlyAccess>): List<AccessWithExclusion<BaseOnlyAccess>> {
                val accessChanged = finals.add(final.access)
                val mergedExclusion = exclusion.union(final.exclusion)
                val exclusionChanged = mergedExclusion != exclusion
                if (!accessChanged && !exclusionChanged) return emptyList()
                exclusion = mergedExclusion
                if (!exclusionChanged) return listOf(AccessWithExclusion(final.access, exclusion))

                return buildList(finals.size) {
                    finals.forEach { add(AccessWithExclusion(it, exclusion)) }
                }
            }

            fun collect(out: (AccessWithExclusion<BaseOnlyAccess>) -> Unit) {
                finals.forEach { out(AccessWithExclusion(it, exclusion)) }
            }
        }

        fun add(
            statement: CommonInst,
            final: AccessWithExclusion<BaseOnlyAccess>,
        ): List<AccessWithExclusion<BaseOnlyAccess>> {
            val idx = instructionStorageIdx(statement, languageManager)
            val current = entries[idx]
            if (current == null) {
                entries[idx] = Entry(final)
                return listOf(final)
            }
            return current.add(final)
        }

        fun collectAt(statement: CommonInst, out: (AccessWithExclusion<BaseOnlyAccess>) -> Unit) {
            entries[instructionStorageIdx(statement, languageManager)]?.collect(out)
        }
    }
}

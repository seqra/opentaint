package org.opentaint.dataflow.ap.ifds.access.baseonly

import it.unimi.dsi.fastutil.longs.Long2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
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
        ): AccessWithExclusion<BaseOnlyAccess>? {
            val ps = perInitial.get(initial)
                ?: PerStatement(maxInstIdx, languageManager, apManager, initial).also { perInitial.put(initial, it) }
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
                // Summary storage exposes field-AP initials as suffix-AP aliases. Resolve that alias
                // against the original key used by the intraprocedural edge store.
                if (initial.apSlot != 2 || finalPattern.apSlot != 2) return
                val fieldInitialAlias = packBaseOnlyAccess(initial.staticIdx, ABSTRACT_MARK, NO_ACCESSOR)
                perInitial[fieldInitialAlias]?.collectAt(statement) { dst.add(it) }
            }
        }
    }

    private class PerStatement(
        maxInstIdx: Int,
        private val languageManager: LanguageManager,
        private val manager: BaseOnlyApManager,
        initial: BaseOnlyAccess,
    ) {
        private val apSlot = maxOf(initial.apSlot, 0)

        private val entries =
            arrayOfNulls<Long2ObjectOpenHashMap<Any>>(instructionStorageSize(maxInstIdx))

        fun add(
            statement: CommonInst,
            final: AccessWithExclusion<BaseOnlyAccess>,
        ): AccessWithExclusion<BaseOnlyAccess>? {
            if (final.access.isCollapsed) return null
            val idx = instructionStorageIdx(statement, languageManager)
            val map = entries[idx] ?: Long2ObjectOpenHashMap<Any>().also { entries[idx] = it }
            val access = final.access
            val incoming = BaseOnlyExclusionOps.fromExclusionSet(final.exclusion, manager.interner, apSlot)
            val cur = map.get(access)
            if (cur == null) {
                map.put(access, incoming)
                return AccessWithExclusion(access, BaseOnlyExclusionOps.toExclusionSet(incoming, manager.interner))
            }
            val merged = BaseOnlyExclusionOps.mergeInPlace(cur, incoming)
            if (!merged.grew) return null
            map.put(access, merged.value)
            return AccessWithExclusion(access, BaseOnlyExclusionOps.toExclusionSet(merged.value, manager.interner))
        }

        fun collectAt(statement: CommonInst, out: (AccessWithExclusion<BaseOnlyAccess>) -> Unit) {
            entries[instructionStorageIdx(statement, languageManager)]?.forEach { (access, value) ->
                out(AccessWithExclusion(access, BaseOnlyExclusionOps.toExclusionSet(value, manager.interner)))
            }
        }
    }
}

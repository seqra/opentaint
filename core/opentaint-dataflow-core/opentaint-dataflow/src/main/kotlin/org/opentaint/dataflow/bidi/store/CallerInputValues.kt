package org.opentaint.dataflow.bidi.store

import it.unimi.dsi.fastutil.objects.Object2IntOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.ir.api.common.cfg.CommonInst

/** Stable native keys with either exact FULL relations or one scalar value as authority. */
internal class CallerInputValues(private val m: ApManager, private val markMode: MarkMode) {
    private data class NativeKey(val ref: CallerRef, val group: GroupKey)
    private data class OriginalGeometry(val manager: ApManager, val base: AccessPathBase,
                                        val path: PathNode?, val tail: Tail, val exclusion: ExclusionSet)
    private data class FamilyKey(val caller: MethodKey, val callerLayer: Layer, val call: CommonInst,
                                 val stageOrdinal: Int, val scope: BlockScope,
                                 val original: OriginalGeometry, val group: GroupKey)
    private class Family(val key: FamilyKey, m: ApManager) {
        val relations = CallerMarkRelations(m)
    }
    private sealed interface Location {
        class Packed(val family: Family, val source: TaintMark) : Location
        class Scalar(var facts: Facts) : Location
    }
    private class Slot(val key: NativeKey, var location: Location)

    private val handles = Object2IntOpenHashMap<NativeKey>().apply { defaultReturnValue(-1) }
    private val slots = ArrayList<Slot>()
    private val families = HashMap<FamilyKey, Family>()
    private val interners = m.newInterners()
    private var decoded = 0L
    private var migrations = 0L

    val size: Int get() = slots.size
    internal val packedFamilyCount: Int get() = families.size
    internal val packedSourceCount: Int get() = families.values.sumOf { it.relations.sourceCount }
    internal val scalarCount: Int get() = slots.count { it.location is Location.Scalar }

    internal data class Census(val logicalGroups: Int, val families: Int, val sources: Int,
                               val cells: Long, val diagonal: Long, val changingPairs: Long,
                               val changingTargets: Long, val scalar: Int, val migrations: Long,
                               val decodedSnapshots: Long)

    /** A joined numeric census. It retains no historical packets or keys. */
    internal fun census(): Census = Census(size, families.size, packedSourceCount,
        families.values.sumOf { it.relations.cellCount.toLong() },
        families.values.sumOf { it.relations.diagonalCount },
        families.values.sumOf { it.relations.changingPairCount },
        families.values.sumOf { it.relations.changingTargetCount }, scalarCount, migrations, decoded)

    fun add(ref: CallerRef, linkLayer: Layer, offered: Facts): AddedFactAccumulator.Update? {
        m.cancellation.checkpoint()
        if (!RuntimeDataDomain.packet(ref.premise, offered)) return null
        check(offered.base !is AccessPathBase.CleanerTemporary) { "A field-action temporary cannot enter an added link" }
        check(linkLayer == offered.layer) { "The link layer must be the added fact's layer" }
        // Retain the original offered header, even when a fresh exact delta clears E/tail.
        val key = NativeKey(ref, offered.groupKey)
        val handle = handles.getInt(key)
        val packed = packable(ref, offered)
        if (handle < 0) {
            val location = if (packed) {
                val initial = ref.premise as InitialAp
                val familyKey = familyKey(key, initial)
                val family = families.getOrPut(familyKey) { Family(familyKey, m) }
                val source = (initial.mark as MarkSlot.Concrete).mark
                family.relations.add(source, (offered as TaintTree).root)
                Location.Packed(family, source)
            } else Location.Scalar(interners.internIfRequired(offered))
            val id = slots.size
            slots += Slot(key, location)
            handles.put(key, id)
            val value = if (location is Location.Scalar) location.facts else offered
            return AddedFactAccumulator.Update(id, AddedFactAccumulator.Snapshot(ref, key.group, value), offered, true)
        }
        val slot = slots[handle]
        val old = snapshot(handle).facts
        val (merged, fresh) = m.mergeAddDelta(old, offered)
        if (fresh == null) return null
        when (val location = slot.location) {
            is Location.Scalar -> location.facts = interners.internIfRequired(merged)
            is Location.Packed -> if (packed) {
                location.family.relations.add(location.source, (fresh as TaintTree).root)
            } else {
                // Keep the handle and its positional postings. Only its value authority moves.
                location.family.relations.remove(location.source)
                if (location.family.relations.sourceCount == 0) families.remove(location.family.key)
                slot.location = Location.Scalar(interners.internIfRequired(merged))
                migrations++
            }
        }
        return AddedFactAccumulator.Update(handle,
            AddedFactAccumulator.Snapshot(slot.key.ref, slot.key.group, merged), fresh, false)
    }

    fun snapshot(handle: Int): AddedFactAccumulator.Snapshot {
        m.cancellation.checkpoint()
        val slot = slots[handle]
        val value = when (val location = slot.location) {
            is Location.Scalar -> location.facts
            is Location.Packed -> {
                decoded++
                val root = location.family.relations.root(location.source)
                val header = slot.key.group
                m.taintTree(header.base, header.layer, root, header.exclusion, header.tail,
                    if (header.protected) root else null)
            }
        }
        return AddedFactAccumulator.Snapshot(slot.key.ref, slot.key.group, value)
    }

    private fun familyKey(key: NativeKey, initial: InitialAp): FamilyKey = FamilyKey(
        key.ref.caller, key.ref.callerLayer, key.ref.call, key.ref.stageOrdinal, key.ref.scope,
        OriginalGeometry(initial.manager, initial.base, initial.path, initial.tail, initial.exclusion), key.group)

    private fun packable(ref: CallerRef, offered: Facts): Boolean {
        if (markMode != MarkMode.FULL || offered !is TaintTree) return false
        val initial = ref.premise as? InitialAp ?: return false
        val source = (initial.mark as? MarkSlot.Concrete)?.mark ?: return false
        if (initial.manager !== m || initial.isZero || !m.marks.isFull(source)) return false
        // Internal producers can offer exact-only roots with a noncanonical any header.
        // Keep the native scalar interning/header behavior for those unsupported shapes.
        if (!offered.root.hasAny && offered.anyTail != Tail.ANY_TAINT) return false
        // The GroupKey above enforces the unchanged uniform-H retained domain.
        val marks = m.taintAlg.foldAll(offered.root, m.cancellation)
        return (marks.exact + marks.any).ids.all { m.marks.isFull(TaintMark(it)) }
    }

    fun clear() {
        handles.clear()
        slots.clear()
        families.clear()
        decoded = 0
        migrations = 0
    }
}

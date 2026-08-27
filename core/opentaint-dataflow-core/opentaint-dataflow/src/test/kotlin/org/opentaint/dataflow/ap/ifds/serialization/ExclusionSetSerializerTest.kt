package org.opentaint.dataflow.ap.ifds.serialization

import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.ir.api.common.CommonMethod
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * The exclusion-set wire format, which three access-path serializers embed inline and positionally.
 *
 * Nothing pinned this format before the read/write split, and there is no version field anywhere in
 * `ap/ifds/serialization` — a silent format change mis-decodes a stale summary store rather than
 * rejecting it. Hence the legacy-decode case below.
 */
class ExclusionSetSerializerTest {
    private val a = FieldAccessor("A", "a", "T")
    private val b = FieldAccessor("A", "b", "T")

    private val context = InMemoryAccessorContext()
    private val serializer = ExclusionSetSerializer(context)

    private fun roundTrip(exclusionSet: ExclusionSet): ExclusionSet {
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { with(serializer) { it.writeExclusionSet(exclusionSet) } }
        return DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use {
            with(serializer) { it.readExclusionSet() }
        }
    }

    @Test
    fun `empty and universe round-trip`() {
        assertEquals(ExclusionSet.Empty, roundTrip(ExclusionSet.Empty))
        assertEquals(ExclusionSet.Universe, roundTrip(ExclusionSet.Universe))
    }

    @Test
    fun `a concrete demand round-trips with its kinds`() {
        val set = ExclusionSet.Empty.addRead(a).addWrite(b)
        val restored = roundTrip(set)

        assertEquals(set, restored)
        assertEquals(set.hashCode(), restored.hashCode())
    }

    @Test
    fun `a demand of a single kind round-trips`() {
        assertEquals(ExclusionSet.Empty.addRead(a), roundTrip(ExclusionSet.Empty.addRead(a)))
        assertEquals(ExclusionSet.Empty.addWrite(a), roundTrip(ExclusionSet.Empty.addWrite(a)))
    }

    @Test
    fun `a read-only demand is written in the pre-split shape`() {
        // There is no schema version on the persisted store and an older build throws on an unknown
        // tag, so the new shape is used only when there is a write demand that needs it.
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use {
            with(serializer) { it.writeExclusionSet(ExclusionSet.Empty.addRead(a)) }
        }
        assertEquals(LEGACY_CONCRETE_TAG, bytes.toByteArray().first().toInt())

        val rw = ByteArrayOutputStream()
        DataOutputStream(rw).use {
            with(serializer) { it.writeExclusionSet(ExclusionSet.Empty.addWrite(a)) }
        }
        assertEquals(LEGACY_CONCRETE_TAG + 1, rw.toByteArray().first().toInt())
    }

    @Test
    fun `a pre-split blob decodes as an all-read demand`() {
        // Format before the split: the CONCRETE tag (ordinal 2), a count, then that many accessor ids.
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use {
            it.write(LEGACY_CONCRETE_TAG)
            it.writeInt(2)
            it.writeLong(context.getIdByAccessor(a))
            it.writeLong(context.getIdByAccessor(b))
        }

        val restored = DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use {
            with(serializer) { it.readExclusionSet() }
        }

        assertEquals(ExclusionSet.Empty.addRead(a).addRead(b), restored)
    }

    private class InMemoryAccessorContext : SummarySerializationContext {
        private val ids = hashMapOf<Accessor, Long>()
        private val accessors = hashMapOf<Long, Accessor>()

        override fun getIdByAccessor(accessor: Accessor): Long =
            ids.getOrPut(accessor) { ids.size.toLong().also { accessors[it] = accessor } }

        override fun getAccessorById(id: Long): Accessor = accessors.getValue(id)

        override fun getIdByMethod(method: CommonMethod): Long = error("Not used")
        override fun getMethodById(id: Long): CommonMethod = error("Not used")
        override fun loadSummaries(method: CommonMethod): ByteArray? = error("Not used")
        override fun storeSummaries(method: CommonMethod, summaries: ByteArray) = error("Not used")
        override fun flush() = error("Not used")
    }

    private companion object {
        private const val LEGACY_CONCRETE_TAG = 2
    }
}

package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.ir.api.common.CommonMethod
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.DataOutputStream
import kotlin.test.Test
import kotlin.test.assertEquals

class BaseOnlySerializerTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val field = FieldAccessor("A", "f", "B")
    private val mark = TaintMarkAccessor("m")

    private val m = BaseOnlyApManager(AnyAccessorUnrollStrategy.AnyAccessorDisabled, fieldSensitive = true)
    private val context = InMemoryContext()
    private val serializer = m.createSerializer(context)

    private fun BaseOnlyApManager.finalOf(exclusions: ExclusionSet, vararg accessors: Accessor): FinalFactAp {
        var f = createFinalAp(arg0, exclusions)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun roundTripFinal(ap: FinalFactAp): FinalFactAp {
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { out -> with(serializer) { out.writeFinalAp(ap) } }
        return DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use { input ->
            with(serializer) { input.readFinalAp() }
        }
    }

    private fun roundTripInitial(ap: InitialFactAp): InitialFactAp {
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { out -> with(serializer) { out.writeInitialAp(ap) } }
        return DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use { input ->
            with(serializer) { input.readInitialAp() }
        }
    }

    @Test
    fun `round trips a final fact with any and mark`() {
        val ap = m.finalOf(ExclusionSet.Empty, field, AnyAccessor, mark)
        assertEquals(ap, roundTripFinal(ap))
    }

    @Test
    fun `round trips an abstract final fact`() {
        val ap = m.mostAbstractFinalAp(arg0)
        assertEquals(ap, roundTripFinal(ap))
    }

    @Test
    fun `round trips a final fact with concrete exclusions`() {
        val ap = m.finalOf(ExclusionSet.Empty, AnyAccessor, mark).exclude(field)
        assertEquals(ap, roundTripFinal(ap))
    }

    @Test
    fun `round trips a final fact with a collapsed type pair`() {
        val ap = m.finalOf(ExclusionSet.Empty, TypeInfoGroupAccessor, TypeInfoAccessor("pkg.fn"))
        assertEquals(ap, roundTripFinal(ap))
    }

    @Test
    fun `round trips an initial fact with final accessor`() {
        val ap = m.createFinalInitialAp(arg0, ExclusionSet.Empty).prependAccessor(mark).prependAccessor(AnyAccessor)
        assertEquals(ap, roundTripInitial(ap))
    }

    private class InMemoryContext : SummarySerializationContext {
        private val accessorToId = HashMap<Accessor, Long>()
        private val idToAccessor = HashMap<Long, Accessor>()

        override fun getIdByAccessor(accessor: Accessor): Long =
            accessorToId.getOrPut(accessor) {
                val id = accessorToId.size.toLong()
                idToAccessor[id] = accessor
                id
            }

        override fun getAccessorById(id: Long): Accessor = idToAccessor.getValue(id)

        override fun getIdByMethod(method: CommonMethod): Long = error("not used")
        override fun getMethodById(id: Long): CommonMethod = error("not used")
        override fun loadSummaries(method: CommonMethod): ByteArray? = error("not used")
        override fun storeSummaries(method: CommonMethod, summaries: ByteArray) = error("not used")
        override fun flush() = error("not used")
    }
}

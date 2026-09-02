package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor
import org.opentaint.dataflow.ap.ifds.ValueAccessor
import org.opentaint.dataflow.ap.ifds.access.AnyAccessorUnrollStrategy
import org.opentaint.dataflow.util.Cancellation
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
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class BaseOnlySerializerTest {
    private val arg0 = AccessPathBase.Argument(0)
    private val field = FieldAccessor("A", "f", "B")
    private val mark = TaintMarkAccessor("m")
    private val stat = ClassStaticAccessor("A")

    private val m = BaseOnlyApManager(
        AnyAccessorUnrollStrategy.AnyAccessorDisabled,
        Cancellation(),
        fieldSensitive = true,
    )
    private val context = InMemoryContext()
    private val serializer = m.createSerializer(context)

    private fun BaseOnlyApManager.finalOf(exclusions: ExclusionSet, vararg accessors: Accessor): FinalFactAp {
        var f = createFinalAp(arg0, exclusions)
        accessors.reversed().forEach { f = f.prependAccessor(it) }
        return f
    }

    private fun roundTripFinal(ap: FinalFactAp): FinalFactAp {
        val encoded = encodeFinal(ap)
        return decodeFinal(encoded)
    }

    private fun encodeFinal(ap: FinalFactAp): ByteArray {
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { out -> with(serializer) { out.writeFinalAp(ap) } }
        return bytes.toByteArray()
    }

    private fun decodeFinal(encoded: ByteArray): FinalFactAp =
        DataInputStream(ByteArrayInputStream(encoded)).use { input ->
            with(serializer) { input.readFinalAp() }
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
    fun `Any is implicit and is not serialized in the field slot`() {
        val anyMark = m.finalOf(ExclusionSet.Empty, AnyAccessor, mark)
        val restored = roundTripFinal(anyMark)

        assertEquals(anyMark, restored)
        assertEquals(NO_ACCESSOR, (restored as BaseOnlyFinalFactAp).access.fieldIdx)
        assertEquals(setOf(AnyAccessor, mark), restored.getStartAccessors())
        assertTrue(restored.startsWithAccessor(mark))
        assertNotNull(restored.readAccessor(AnyAccessor))
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
    fun `round trips normal and value states for taint and type terminals`() {
        val terminals = listOf(
            m.finalOf(ExclusionSet.Empty, mark) as BaseOnlyFinalFactAp,
            m.finalOf(ExclusionSet.Empty, ValueAccessor, mark) as BaseOnlyFinalFactAp,
            m.finalOf(ExclusionSet.Empty, TypeInfoAccessor("pkg.direct")) as BaseOnlyFinalFactAp,
            m.finalOf(
                ExclusionSet.Empty, TypeInfoGroupAccessor, TypeInfoAccessor("pkg.wrapped"),
            ) as BaseOnlyFinalFactAp,
        )
        for (expected in terminals) {
            val restored = roundTripFinal(expected) as BaseOnlyFinalFactAp
            assertEquals(expected, restored)
            assertEquals(expected.access.valueAccessorState, restored.access.valueAccessorState)
        }
    }

    @Test
    fun `deserializer rejects a lone value wrapper as a terminal`() {
        val localContext = InMemoryContext()
        val localSerializer = m.createSerializer(localContext)
        val direct = m.finalOf(ExclusionSet.Empty, mark)
        val bytes = ByteArrayOutputStream()
        DataOutputStream(bytes).use { out -> with(localSerializer) { out.writeFinalAp(direct) } }
        val markId = localContext.getIdByAccessor(mark)
        localContext.replaceAccessor(markId, ValueAccessor)
        assertFailsWith<IllegalArgumentException> {
            DataInputStream(ByteArrayInputStream(bytes.toByteArray())).use { input ->
                with(localSerializer) { input.readFinalAp() }
            }
        }
    }

    @Test
    fun `round trips an initial fact with final accessor`() {
        val ap = m.createFinalInitialAp(arg0, ExclusionSet.Empty).prependAccessor(mark).prependAccessor(AnyAccessor)
        assertEquals(ap, roundTripInitial(ap))
    }

    @Test
    fun `round trips every abstraction slot without rebuilding the path and rejects transient collapsed state`() {
        val statIdx = m.interner.index(stat)
        val fieldIdx = m.interner.index(field)
        val accesses = listOf(
            BaseOnlyAccessOps.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0),
            BaseOnlyAccessOps.abstractAt(statIdx, NO_ACCESSOR, 1),
            BaseOnlyAccessOps.abstractAt(statIdx, fieldIdx, 2),
        )

        for (access in accesses) {
            val final = BaseOnlyFinalFactAp(m, arg0, access, ExclusionSet.Empty)
            val initial = BaseOnlyInitialFactAp(m, arg0, access, ExclusionSet.Empty)
            assertEquals(final, roundTripFinal(final), "final access $access")
            assertEquals(initial, roundTripInitial(initial), "initial access $access")
        }

        val transient = BaseOnlyFinalFactAp(
                m,
                arg0,
                BaseOnlyAccessOps.collapse(BaseOnlyAccessOps.abstractAt(statIdx, fieldIdx, 2)),
                ExclusionSet.Empty,
            )
        assertFailsWith<IllegalArgumentException> {
            roundTripFinal(transient)
        }
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

        fun replaceAccessor(id: Long, accessor: Accessor) {
            idToAccessor[id] = accessor
        }

        override fun getIdByMethod(method: CommonMethod): Long = error("not used")
        override fun getMethodById(id: Long): CommonMethod = error("not used")
        override fun loadSummaries(method: CommonMethod): ByteArray? = error("not used")
        override fun storeSummaries(method: CommonMethod, summaries: ByteArray) = error("not used")
        override fun flush() = error("not used")
    }
}

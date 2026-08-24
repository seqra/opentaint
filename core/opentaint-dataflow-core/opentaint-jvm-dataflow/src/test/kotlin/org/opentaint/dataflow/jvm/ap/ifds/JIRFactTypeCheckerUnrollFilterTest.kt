package org.opentaint.dataflow.jvm.ap.ifds

import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FilterResult
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.jvm.BasicTestUtils
import kotlin.test.Test
import kotlin.test.assertEquals

/**
 * The any-accessor unroll asks [JIRFactTypeChecker.accessPathFilter] whether a candidate field may
 * follow a prefix, and the filter's whole discriminating power comes from the declared `fieldType`
 * of the prefix's last accessor. Every field modifier emitted by `model/java/config` declares
 * `java.lang.Object` as that type, so these tests pin what the filter can still reject once a path
 * has crossed one modelled field.
 */
class JIRFactTypeCheckerUnrollFilterTest : BasicTestUtils() {
    private val typeChecker by lazy { JIRFactTypeChecker(cp) }

    /** Exactly the shape `model/java/config` emits: `.java.lang.Iterable#Element#java.lang.Object`. */
    private val modelElementField =
        FieldAccessor(className = "java.lang.Iterable", fieldName = "Element", fieldType = "java.lang.Object")

    /** A field of a final class that no `Iterable` element can ever be. */
    private val unrelatedField =
        FieldAccessor(className = "java.net.URL", fieldName = "host", fieldType = "java.lang.Object")

    /** The shape main's config still used for 1844 modifiers, e.g. `#java.lang.String`. */
    private val concretelyTypedField =
        FieldAccessor(className = "java.lang.StringBuilder", fieldName = "value", fieldType = "java.lang.String")

    @Test
    fun `concrete field type rejects an unrelated field`() {
        val filter = typeChecker.accessPathFilter(listOf(concretelyTypedField))

        assertEquals(FilterResult.Reject, filter.check(unrelatedField))
    }

    @Test
    fun `object typed model field rejects an unrelated field`() {
        val filter = typeChecker.accessPathFilter(listOf(modelElementField))

        assertEquals(FilterResult.Reject, filter.check(unrelatedField))
    }

    @Test
    fun `chained model fields reject an unrelated field`() {
        val filter = typeChecker.accessPathFilter(listOf(modelElementField, modelElementField))

        assertEquals(FilterResult.Reject, filter.check(unrelatedField))
    }
}

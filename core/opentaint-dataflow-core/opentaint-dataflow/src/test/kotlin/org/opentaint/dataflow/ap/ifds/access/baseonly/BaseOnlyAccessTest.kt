package org.opentaint.dataflow.ap.ifds.access.baseonly

import org.opentaint.dataflow.ap.ifds.AnyAccessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertTrue

class BaseOnlyAccessTest {
    private val accessors = AccessorInterner()
    private val ai = BaseOnlyAccessOps

    private val field = FieldAccessor("A", "f", "B")
    private val field2 = FieldAccessor("A", "g", "B")
    private val mark = TaintMarkAccessor("m")
    private val mark2 = TaintMarkAccessor("n")
    private val stat = ClassStaticAccessor("T")
    private val stat2 = ClassStaticAccessor("U")
    private val final = FinalAccessor

    private fun i(a: org.opentaint.dataflow.ap.ifds.Accessor) = accessors.index(a)

    private fun chain(vararg a: org.opentaint.dataflow.ap.ifds.Accessor, abstract: Boolean = false): BaseOnlyAccess =
        ai.build(IntArray(a.size) { i(a[it]) }, abstract)

    @Test
    fun `equal chains produce equal packed values`() {
        assertEquals(chain(mark), chain(mark))
        assertEquals(chain(AnyAccessor, mark), chain(AnyAccessor, mark))
    }

    @Test
    fun `field absorbed by any when field-insensitive`() {
        val base = chain(AnyAccessor, mark)
        assertEquals(base, ai.prepend(base, i(field), fieldSensitive = false))
    }

    @Test
    fun `field kept before any when field-sensitive`() {
        val base = chain(AnyAccessor, mark)
        assertEquals(chain(field, AnyAccessor, mark), ai.prepend(base, i(field), fieldSensitive = true))
    }

    @Test
    fun `second field replaces first`() {
        val f1 = chain(field, AnyAccessor, mark)
        assertEquals(chain(field2, AnyAccessor, mark), ai.prepend(f1, i(field2), fieldSensitive = true))
    }

    @Test
    fun `class static goes before field`() {
        val base = chain(field, AnyAccessor, mark)
        assertEquals(chain(stat, field, AnyAccessor, mark), ai.prepend(base, i(stat), fieldSensitive = true))
    }

    @Test
    fun `prepend taint keeps canonical order behind static`() {
        val base = chain(stat)
        assertEquals(chain(stat, mark), ai.prepend(base, i(mark), fieldSensitive = false))
    }

    @Test
    fun `read field off abstract stays abstract`() {
        val abstract = ai.abstractEmpty
        assertEquals(abstract, ai.read(abstract, i(field)))
    }

    @Test
    fun `read any off abstract stays abstract`() {
        val abstract = ai.abstractEmpty
        assertEquals(abstract, ai.read(abstract, i(AnyAccessor)))
    }

    @Test
    fun `read field off final is null`() {
        assertNull(ai.read(chain(final), i(field)))
    }

    @Test
    fun `read field off taint stays covering`() {
        val taint = chain(mark)
        assertEquals(taint, ai.read(taint, i(field)))
    }

    @Test
    fun `read matching taint drops it to final`() {
        assertEquals(chain(final), ai.read(chain(mark), i(mark)))
    }

    @Test
    fun `read matching field off field-abstract stays abstract`() {
        val fieldAbstract = ai.prepend(ai.abstractEmpty, i(field), fieldSensitive = true)
        assertEquals(ai.abstractEmpty, ai.read(fieldAbstract, i(field)))
    }

    @Test
    fun `startsWith any structural is true for abstract and taint but not value`() {
        assertTrue(ai.startsWith(ai.abstractEmpty, i(field)))
        assertFalse(ai.startsWith(chain(final), i(field)))
        assertTrue(ai.startsWith(chain(mark), i(field)))
    }

    @Test
    fun `append keeps suffix abstraction when prefix has no terminal`() {
        assertEquals(ai.abstractEmpty, ai.append(ai.empty, ai.abstractEmpty))
    }

    @Test
    fun `append keeps prefix taint over abstract suffix`() {
        assertEquals(chain(mark), ai.append(chain(mark), ai.abstractEmpty))
    }

    @Test
    fun `abstract initial yields whole final as delta`() {
        val match = ai.matchPrefix(chain(mark), ai.abstractEmpty)
        assertFalse(match.emptyDelta)
        assertTrue(match.hasSuffix)
        assertEquals(chain(mark), match.suffix)
    }

    @Test
    fun `taint initial does not match bare final`() {
        val match = ai.matchPrefix(chain(final), chain(mark))
        assertFalse(match.emptyDelta)
        assertFalse(match.hasSuffix)
    }

    @Test
    fun `read AP-position mirror`() {
        val f1 = i(field); val t1 = i(mark); val dollar = i(final)

        // value strict: read field off value -> null (getter-alias removed)
        assertNull(ai.read(chain(final), f1))
        // mark fact: read field idempotent ([any] absorbs); read own mark -> value
        assertEquals(chain(mark), ai.read(chain(mark), f1))
        assertEquals(chain(final), ai.read(chain(mark), t1))
        // suffix-AP: read field idempotent; read mark -> null (must refine, not fabricate)
        assertEquals(ai.abstractEmpty, ai.read(ai.abstractEmpty, f1))
        assertNull(ai.read(ai.abstractEmpty, t1))
        // field-AP: read field -> null (refine); static-AP: read anything -> null
        assertNull(ai.read(ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1), f1))
        assertNull(ai.read(ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0), t1))
        // committed static advances
        assertEquals(ai.abstractEmpty, ai.read(ai.abstractAt(i(stat), NO_ACCESSOR, 2), i(stat)))
    }

    @Test
    fun `startsWith AP-position truth table`() {
        val s1 = i(stat); val s2 = i(stat2); val f1 = i(field)
        val t1 = i(mark); val t2 = i(mark2); val dollar = i(final)

        // (ABSTRACT,-1,-1) — AP at static: nothing matches (all refine)
        val apStatic = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        for (q in listOf(s1, s2, f1, t1, dollar)) assertFalse(ai.startsWith(apStatic, q), "apStatic sw $q")

        // (s1, ABSTRACT, -1) — committed s1, AP at field: only s1
        val s1FieldAp = ai.abstractAt(s1, NO_ACCESSOR, 1)
        assertTrue(ai.startsWith(s1FieldAp, s1)); assertFalse(ai.startsWith(s1FieldAp, s2))
        assertFalse(ai.startsWith(s1FieldAp, f1)); assertFalse(ai.startsWith(s1FieldAp, t1))

        // (s1, f1, ABSTRACT) — committed s1.f1, AP at suffix: only s1 at the head
        val s1f1SuffAp = ai.abstractAt(s1, f1, 2)
        assertTrue(ai.startsWith(s1f1SuffAp, s1)); assertFalse(ai.startsWith(s1f1SuffAp, f1))
        assertFalse(ai.startsWith(s1f1SuffAp, t1))

        // (-1, ABSTRACT, -1) — AP at field, no static: static false, field false, mark false
        val fieldAp = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 1)
        assertFalse(ai.startsWith(fieldAp, s1)); assertFalse(ai.startsWith(fieldAp, f1))
        assertFalse(ai.startsWith(fieldAp, t1))

        // (-1, -1, ABSTRACT) — AP at suffix: field true ([any]), mark false, static false
        val suffAp = ai.abstractEmpty
        assertTrue(ai.startsWith(suffAp, f1)); assertFalse(ai.startsWith(suffAp, t1))
        assertFalse(ai.startsWith(suffAp, s1))

        // concrete mark x.!t1.$ : field true ([any]), own mark true, other mark false, $ false (behind mark)
        val markFact = chain(mark)
        assertTrue(ai.startsWith(markFact, f1)); assertTrue(ai.startsWith(markFact, t1))
        assertFalse(ai.startsWith(markFact, t2)); assertFalse(ai.startsWith(markFact, dollar))

        // value x.$ : strict — only $
        val valueFact = chain(final)
        assertTrue(ai.startsWith(valueFact, dollar)); assertFalse(ai.startsWith(valueFact, f1))
        assertFalse(ai.startsWith(valueFact, t1))
    }

    @Test
    fun `collapse clears exactly the abstract slot and keeps the rest`() {
        val staticAbstract = ai.abstractAt(NO_ACCESSOR, NO_ACCESSOR, 0)
        assertEquals(0, staticAbstract.apSlot)
        val staticCollapsed = ai.collapse(staticAbstract)
        assertEquals(NO_ACCESSOR, staticCollapsed.staticIdx)
        assertFalse(staticCollapsed.isCollapsed)
        assertEquals(ai.empty, staticCollapsed)

        val fieldAbstract = ai.abstractAt(i(stat), NO_ACCESSOR, 1)
        assertEquals(1, fieldAbstract.apSlot)
        val fieldCollapsed = ai.collapse(fieldAbstract)
        assertEquals(i(stat), fieldCollapsed.staticIdx)
        assertEquals(NO_ACCESSOR, fieldCollapsed.fieldIdx)
        assertFalse(fieldCollapsed.isCollapsed)

        val suffixAbstract = ai.abstractAt(i(stat), i(field), 2)
        assertEquals(2, suffixAbstract.apSlot)
        val suffixCollapsed = ai.collapse(suffixAbstract)
        assertTrue(suffixCollapsed.isCollapsed)
        assertEquals(i(stat), suffixCollapsed.staticIdx)
        assertEquals(i(field), suffixCollapsed.fieldIdx)

        val concrete = chain(mark)
        assertEquals(-1, concrete.apSlot)
        assertEquals(concrete, ai.collapse(concrete))
    }
}

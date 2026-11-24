package org.opentaint.dataflow.jvm.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FilterResult
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.bidi.fixtures.jvmTestDeclarations
import org.opentaint.dataflow.jvm.bidi.interp.JIRTypeFilters
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.JIRType
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNull
import kotlin.test.assertSame
import kotlin.test.assertTrue

/**
 * The production type filters (JIRTypeFilters.make) on real JIR types, for the String chain fixtures
 * (G6DropFormFixtureTest in opentaint-dataflow, from proto/string-chain-fixture-20261120).
 *
 * 1. The decision rows of the fixture replica (G6DropFormFixtureTest.ModelType) equal the rows of the real filters.
 * 2. The String fields that the JIR model exposes.
 * 3. A K-cut replaces the part of a fact below depth K by an ANY leaf: the cut fact has a PREFIX of the exact path.
 *    Exhaustive check over types x paths (length <= 3) x marks: the `may` filter (checker.localFilter) is prefix-closed
 *    (ap.md S5), and so is the full filter with the mark policy (G6 drop form, spec/acyclic-group-a-implementation.md
 *    §3): a boxed value (Integer, Character, Long, Boolean) loses an ordinary mark on every leaf, so no type keeps an
 *    exact fact and drops a cut prefix of it.
 */
class JIRStringChainFiltersTest : BasicTestUtils() {
    private val manager = ApManager(Cancellation(), marks = MarkTable(jvmTestDeclarations()))
    private val ops = ApOps(manager)
    private val checker by lazy { JIRFactTypeChecker(cp) }
    private val filters by lazy { JIRTypeFilters(checker, manager) }
    private val ordinary = manager.marks.mark("T")
    private val tracked = manager.marks.mark("T%%primitive%%")
    private val x = AccessPathBase.Argument(0)
    private val sample = "sample.bidi.BidiStatementSample"

    /** The accessors of StringChainFixtureTest.Acc; the user class is the sample class here. */
    private val fixtureAccessors: List<Pair<String, Accessor>> = listOf(
        "S_VALUE" to FieldAccessor("java.lang.String", "value", "byte[]"),
        "S_CODER" to FieldAccessor("java.lang.String", "coder", "byte"),
        "S_HASH" to FieldAccessor("java.lang.String", "hash", "int"),
        "I_VALUE" to FieldAccessor("java.lang.Integer", "value", "int"),
        "E" to ElementAccessor,
        "LIST_ELEMENT" to FieldAccessor("java.lang.Iterable", "Element", "java.lang.Object"),
        "MAP_VALUE" to FieldAccessor("java.util.Map", "MapValue", "java.lang.Object"),
        "BOX_VALUE" to FieldAccessor(sample, "f", "java.lang.Object"),
    )

    private fun type(name: String): JIRType = cp.findTypeOrNull(name) ?: error("Missing test type $name")
    private fun filter(name: String): TypeFilter = requireNotNull(filters.of(type(name)))
    private fun facts(path: List<Accessor>, tail: Tail, mark: TaintMark, layer: Layer) =
        manager.factsOf(PathFact(x, path.map(manager.accessors::index), tail, MarkSlot.Concrete(mark)), ExclusionSet.Empty, layer)
    private fun levels(name: String): List<String> = generateSequence(name) { if (it.endsWith("[]")) it.removeSuffix("[]") else null }.toList()

    /** The same row format as StringChainFixtureTest.ModelType.signature. */
    private fun signature(name: String): String {
        val f = filter(name)
        val may = fixtureAccessors.joinToString(" ") { (label, a) ->
            "$label=" + when (val r = f.may.check(a)) {
                FilterResult.Accept -> "A"
                FilterResult.Reject -> "R"
                is FilterResult.FilterNext -> {
                    val element = name.removeSuffix("[]")
                    assertEquals(checker.localFilter(type(element)), r.filter, "$name element filter")
                    "N:$element"
                }
            }
        }
        val policy = f.markPolicy?.let { p ->
            levels(name).indices.joinToString(",") { k ->
                when {
                    p.keeps(ordinary, k) -> "-"
                    p.boxedLevel(k) -> "boxed"
                    else -> "prim"
                }
            }
        } ?: "null"
        return "$may policy=$policy"
    }

    @Test
    fun `the production filters give the decision rows of the fixture replica`(): Unit {
        val expected = mapOf(
            "java.lang.String" to "S_VALUE=A S_CODER=A S_HASH=A I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            "java.lang.String[]" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:java.lang.String LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            "java.lang.String[][]" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:java.lang.String[] LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            "java.lang.Integer" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=A E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=boxed",
            "java.lang.Number" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=A E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            "java.lang.Object" to "S_VALUE=A S_CODER=A S_HASH=A I_VALUE=A E=A LIST_ELEMENT=A MAP_VALUE=A BOX_VALUE=A policy=null",
            "java.util.List" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=A MAP_VALUE=R BOX_VALUE=R policy=null",
            "java.util.Map" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=A BOX_VALUE=R policy=null",
            "int" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=prim",
            "int[]" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:int LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,prim",
            "byte[]" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:byte LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,prim",
            "char[]" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:char LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,prim",
            "java.lang.Integer[]" to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:java.lang.Integer LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,boxed",
            sample to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=A policy=null",
        )
        val actual = expected.keys.associateWith(::signature)
        actual.forEach { (name, row) -> println("STRING_CHAIN_FILTER $name $row") }
        assertEquals(expected, actual)
        // String: no mark policy; `may` is checker.localFilter(String) itself.
        val string = filter("java.lang.String")
        assertNull(string.markPolicy)
        assertEquals(checker.localFilter(type("java.lang.String")), string.may)
        // The cut leaf at the root of a String value (ANY tail, DEMAND) passes with both marks; so do the exact facts.
        for (mark in listOf(ordinary, tracked)) {
            val cut = facts(emptyList(), Tail.ANY, mark, Layer.DEMAND)
            assertSame(cut, ops.filter(cut, string))
            for ((label, a) in fixtureAccessors.take(3)) {
                val exact = facts(listOf(a), Tail.EXACT, mark, Layer.NORMAL)
                assertSame(exact, ops.filter(exact, string), label)
            }
        }
    }

    @Test
    fun `the JIR model of String has the instance fields value coder and hash`(): Unit {
        val fields = findClass("java.lang.String").declaredFields.filter { !it.isStatic }.associate { it.name to it.type.typeName }
        println("STRING_CHAIN_STRING_FIELDS $fields")
        assertEquals("byte[]", fields["value"])
        assertEquals("byte", fields["coder"])
        assertEquals("int", fields["hash"])
        assertEquals(type("byte[]"), checker.fieldAccessorType(fixtureAccessors[0].second as FieldAccessor))
    }

    @Test
    fun `cut prefixes - the may filter and the full filter are prefix-closed`(): Unit {
        val types = listOf(
            "java.lang.String", "java.lang.String[]", "java.lang.String[][]", "java.lang.Object", "java.lang.Object[]",
            "java.lang.Number", "java.lang.Number[]", "java.lang.CharSequence", "java.lang.Comparable", "java.io.Serializable",
            "java.util.List", "java.util.Map", sample,
            "int", "byte", "char", "long", "boolean", "int[]", "byte[]", "char[]", "int[][]",
            "java.lang.Integer", "java.lang.Character", "java.lang.Long", "java.lang.Boolean",
            "java.lang.Integer[]", "java.lang.Integer[][]", "java.lang.Character[]",
        )
        val alphabet = fixtureAccessors.map { it.second } + listOf(
            FieldAccessor("java.lang.Character", "value", "char"),
            FieldAccessor("java.lang.Long", "value", "long"),
            FieldAccessor("java.lang.Boolean", "value", "boolean"),
        )
        val paths = ArrayList<List<Accessor>>()
        var layer = listOf(emptyList<Accessor>())
        repeat(3) { layer = layer.flatMap { p -> alphabet.map { p + it } }; paths += layer }
        data class Break(val type: String, val exact: List<Accessor>, val prefix: Int, val mark: String)
        val mayBreaks = ArrayList<Break>()
        val fullBreaks = ArrayList<Break>()
        var kept = 0
        for (name in types) {
            val full = filter(name)
            val mayOnly = TypeFilter(full.may)
            for (path in paths) for (mark in listOf(ordinary, tracked)) {
                for ((f, out) in listOf(mayOnly to mayBreaks, full to fullBreaks)) {
                    if (ops.filter(facts(path, Tail.EXACT, mark, Layer.NORMAL), f) == null) continue
                    if (f === full) kept++
                    for (k in path.indices) {
                        val cut = facts(path.subList(0, k), Tail.ANY, mark, Layer.DEMAND)
                        if (ops.filter(cut, f) == null) out += Break(name, path, k, manager.marks.name(mark))
                    }
                }
            }
        }
        println("STRING_CHAIN_PREFIX kept exact facts=$kept may breaks=${mayBreaks.size} full breaks=${fullBreaks.size}")
        fullBreaks.groupBy { it.type }.forEach { (t, b) ->
            println("STRING_CHAIN_PREFIX type=$t breaks=${b.size} prefixes=${b.map { it.prefix }.toSortedSet()} marks=${b.map { it.mark }.toSet()} " +
                "sample=${b.first().exact}@${b.first().prefix}")
        }
        assertTrue(mayBreaks.isEmpty(), "may is not prefix-closed: ${mayBreaks.take(10)}")
        // G6 drop form: no type breaks a cut prefix, a boxed level included.
        assertTrue(fullBreaks.isEmpty(), "the mark policy is not prefix-closed: ${fullBreaks.take(10)}")
    }
}

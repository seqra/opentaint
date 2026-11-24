package org.opentaint.dataflow.jvm.bidi

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.interp.ReferenceAlgebra
import org.opentaint.dataflow.jvm.BasicTestUtils
import org.opentaint.dataflow.jvm.ap.ifds.JIRFactTypeChecker
import org.opentaint.dataflow.jvm.bidi.fixtures.jvmTestDeclarations
import org.opentaint.dataflow.jvm.bidi.interp.JIRTypeFilters
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.ir.api.jvm.JIRType
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

/**
 * G6 drop form (spec/acyclic-group-a-implementation.md §3, R1) on the production type filters (JIRTypeFilters.make) of
 * real JIR types: 29 types, all paths of length <= 3 over 12 accessors (the String, Integer, Character, Long and Boolean
 * fields, the element, the collection model fields, a user field and a class-static accessor), the marks `T` and
 * `T%%primitive%%`. A cut form of an exact fact `x.p` is the ANY-tail DEMAND fact `x.q.[any]` for a proper prefix q of
 * p (the K-cut, ap/Limit.kt). An exact fact is checked on both layers. Only facts that the path filter (`may`) keeps are
 * mark-policy cases.
 *
 * - P1 PREFIX-CLOSED (ap.md S5 for the whole filter): the filter keeps an exact fact => it keeps every cut form of it.
 * - P2 BOXED COHERENCE: the filter drops an exact fact at or below a boxed level [e]^b => it drops every cut form of it
 *   at or below [e]^b. A boxed value is decided by the mark only.
 * - P3 CUT KEPT, EXACT DROPPED: if the filter keeps a cut form `x.q.[any]` and drops an exact fact `x.p` below it, then
 *   q is strictly above the level where the exact fact loses the mark (the over-approximating direction).
 * - P4 the mark policy never removes a primitive-tracking mark: the filter decides it as the path filter does.
 * - P5 for a type with no boxed level, a position below a field keeps every mark that the path filter keeps.
 * - P6 the runtime filter (ap/Filter.kt) and the per-path reference (ReferenceAlgebra.passes) agree on every fact.
 *
 * With the class-static accessor in the alphabet, P1 and P2 also cover A2 (no accessor follows a true primitive value).
 */
class JIRG6DropPrefixTest : BasicTestUtils() {
    private val manager = ApManager(Cancellation(), marks = MarkTable(jvmTestDeclarations()))
    private val ops = ApOps(manager)
    private val checker by lazy { JIRFactTypeChecker(cp) }
    private val filters by lazy { JIRTypeFilters(checker, manager) }
    private val reference by lazy { ReferenceAlgebra(ApMode(run1 = true, Direction.FORWARD, fieldLimit = Int.MAX_VALUE), manager = manager) }
    private val ordinary = manager.marks.mark("T")
    private val tracked = manager.marks.mark("T%%primitive%%")
    private val x = AccessPathBase.Argument(0)
    private val sample = "sample.bidi.BidiStatementSample"

    private val types = listOf(
        "java.lang.String", "java.lang.String[]", "java.lang.String[][]", "java.lang.Object", "java.lang.Object[]",
        "java.lang.Number", "java.lang.Number[]", "java.lang.CharSequence", "java.lang.Comparable", "java.io.Serializable",
        "java.util.List", "java.util.Map", sample,
        "int", "byte", "char", "long", "boolean", "int[]", "byte[]", "char[]", "int[][]",
        "java.lang.Integer", "java.lang.Character", "java.lang.Long", "java.lang.Boolean",
        "java.lang.Integer[]", "java.lang.Integer[][]", "java.lang.Character[]",
    )
    private val alphabet: List<Accessor> = listOf(
        FieldAccessor("java.lang.String", "value", "byte[]"),
        FieldAccessor("java.lang.String", "coder", "byte"),
        FieldAccessor("java.lang.String", "hash", "int"),
        FieldAccessor("java.lang.Integer", "value", "int"),
        ElementAccessor,
        FieldAccessor("java.lang.Iterable", "Element", "java.lang.Object"),
        FieldAccessor("java.util.Map", "MapValue", "java.lang.Object"),
        FieldAccessor(sample, "f", "java.lang.Object"),
        FieldAccessor("java.lang.Character", "value", "char"),
        FieldAccessor("java.lang.Long", "value", "long"),
        FieldAccessor("java.lang.Boolean", "value", "boolean"),
        ClassStaticAccessor(sample),
    )
    private val boxedTypes = setOf("java.lang.Integer", "java.lang.Character", "java.lang.Long", "java.lang.Boolean")
    private val primitiveTypes = setOf("int", "byte", "char", "long", "boolean")

    private fun type(name: String): JIRType = cp.findTypeOrNull(name) ?: error("Missing test type $name")
    private fun filter(name: String): TypeFilter = requireNotNull(filters.of(type(name)))
    private fun fact(path: List<Accessor>, tail: Tail, mark: TaintMark) =
        PathFact(x, path.map(manager.accessors::index), tail, MarkSlot.Concrete(mark))
    private fun levels(name: String): List<String> = generateSequence(name) { if (it.endsWith("[]")) it.removeSuffix("[]") else null }.toList()
    private fun spine(path: List<Accessor>): Int = path.indexOfFirst { it != ElementAccessor }.let { if (it < 0) path.size else it }
    /** The boxed spine level at or above the position of [path] in a value of [name], or null. */
    private fun boxedLevel(name: String, path: List<Accessor>): Int? =
        levels(name).withIndex().firstOrNull { (k, t) -> t in boxedTypes && k <= spine(path) }?.index

    private data class Case(val type: String, val path: List<Accessor>, val prefix: Int, val mark: String, val layer: Layer) {
        override fun toString() = "$type ${path.joinToString("") {
            when (it) {
                ElementAccessor -> "[e]"
                is FieldAccessor -> "." + it.fieldName
                else -> ".$it"
            }
        }}@$prefix $mark $layer"
    }

    @Test
    fun `G6 drop form - the production mark policy is prefix-closed`(): Unit {
        val paths = ArrayList<List<Accessor>>()
        var layer = listOf(emptyList<Accessor>())
        paths += layer
        repeat(3) { layer = layer.flatMap { p -> alphabet.map { p + it } }; paths += layer }
        val mayBreaks = ArrayList<Case>()
        val p1 = ArrayList<Case>()
        val p2 = ArrayList<Case>()
        val p3 = ArrayList<Case>()
        val p3Bad = ArrayList<Case>()
        val p4 = ArrayList<Case>()
        val p5 = ArrayList<Case>()
        val p6 = ArrayList<String>()
        var exactKept = 0
        var fieldDrops = 0
        var cutsChecked = 0
        for (name in types) {
            val full = filter(name)
            val mayOnly = TypeFilter(full.may)
            val hasBoxed = levels(name).any { it in boxedTypes }
            val cutDecision = HashMap<Pair<List<Accessor>, TaintMark>, Pair<Boolean, Boolean>>()   // (prefix, mark) -> (full, may)
            fun decide(f: PathFact, layer: Layer, filter: TypeFilter): Boolean {
                val runtime = ops.filter(manager.factsOf(f, ExclusionSet.Empty, layer), filter) != null
                val ref = reference.passes(filter, Conclusion(f, ExclusionSet.Empty, layer == Layer.DEMAND))
                if (runtime != ref) p6 += "$name ${f.path} ${f.tail} $layer runtime=$runtime reference=$ref"
                return runtime
            }
            for (path in paths) for (mark in listOf(ordinary, tracked)) for (exactLayer in listOf(Layer.NORMAL, Layer.DEMAND)) {
                val markName = manager.marks.name(mark)
                val exact = fact(path, Tail.EXACT, mark)
                if (!decide(exact, exactLayer, mayOnly)) continue          // `may` drops it: not a mark-policy case
                val kept = decide(exact, exactLayer, full)
                val belowField = path.any { it != ElementAccessor }
                if (kept) exactKept++
                else if (belowField) fieldDrops++
                // P4: a kept-by-may fact with a primitive-tracking mark stays. P5: no boxed level, below a field.
                if (!kept && mark == tracked) p4 += Case(name, path, path.size, markName, exactLayer)
                if (!kept && !hasBoxed && belowField) p5 += Case(name, path, path.size, markName, exactLayer)
                val boxed = boxedLevel(name, path)
                for (k in path.indices) {
                    val prefix = path.subList(0, k)
                    val (cutKept, cutMay) = cutDecision.getOrPut(prefix to mark) {
                        val cut = fact(prefix, Tail.ANY, mark)
                        decide(cut, Layer.DEMAND, full) to decide(cut, Layer.DEMAND, mayOnly)
                    }
                    cutsChecked++
                    val case = Case(name, path, k, markName, exactLayer)
                    if (!cutMay) mayBreaks += case
                    if (kept && !cutKept) p1 += case
                    if (!kept && boxed != null && k >= boxed && cutKept) p2 += case
                    if (!kept && cutKept) {
                        p3 += case
                        // The level where the exact fact loses the mark: the first primitive or boxed spine level.
                        val loses = levels(name).withIndex().firstOrNull { (j, t) -> j <= spine(path) && (t in boxedTypes || t in primitiveTypes) }?.index
                        if (loses == null || k >= loses) p3Bad += case
                    }
                    if (!cutKept && mark == tracked) p4 += case
                    if (!cutKept && !hasBoxed && prefix.any { it != ElementAccessor }) p5 += case
                }
            }
        }
        println("G6_DROP_PREFIX types=${types.size} paths=${paths.size} marks=2 layers=2; exact facts that may keeps and the filter keeps: " +
            "$exactKept; dropped below a field=$fieldDrops; cut checks=$cutsChecked")
        println("G6_DROP_PREFIX P1=${p1.size} P2=${p2.size} P3 (cut kept above the level)=${p3.size} P3 bad=${p3Bad.size} " +
            "P4=${p4.size} P5=${p5.size} P6=${p6.size}")
        p3.groupBy { it.type }.forEach { (t, b) -> println("G6_DROP_PREFIX P3 type=$t n=${b.size} prefixes=${b.map { it.prefix }.toSortedSet()} sample=${b.first()}") }
        assertTrue(mayBreaks.isEmpty(), "the path filter is prefix-closed: ${mayBreaks.take(10)}")
        assertTrue(p1.isEmpty(), "P1 prefix-closed: ${p1.take(10)}")
        assertTrue(p2.isEmpty(), "P2 boxed coherence: ${p2.take(10)}")
        assertTrue(p3Bad.isEmpty(), "P3 a kept cut covers a dropped exact fact at or below its level: ${p3Bad.take(10)}")
        assertTrue(p4.isEmpty(), "P4 primitive-tracking marks: ${p4.take(10)}")
        assertTrue(p5.isEmpty(), "P5 types without a boxed level: ${p5.take(10)}")
        assertTrue(p6.isEmpty(), "P6 runtime vs reference: ${p6.take(10)}")
        assertTrue(fieldDrops > 0, "the drop form drops the field leaves below a boxed level")
    }

    @Test
    fun `G6 drop form - a boxed value carries only primitive-tracking marks, on both layers`(): Unit {
        val iValue = FieldAccessor("java.lang.Integer", "value", "int")
        val shapes = listOf(
            "java.lang.Integer" to listOf<Accessor>(iValue),
            "java.lang.Integer[]" to listOf(ElementAccessor, iValue),
            "java.lang.Integer[][]" to listOf(ElementAccessor, ElementAccessor, iValue),
        )
        for ((name, path) in shapes) for (layer in listOf(Layer.NORMAL, Layer.DEMAND)) {
            val f = filter(name)
            // ordinary mark: dropped below and at the boxed level, in every form; kept above it.
            assertEquals(null, ops.filter(manager.factsOf(fact(path, Tail.EXACT, ordinary), ExclusionSet.Empty, layer), f), "$name $layer exact")
            for (k in path.indices) {
                val cut = manager.factsOf(fact(path.subList(0, k), Tail.ANY, ordinary), ExclusionSet.Empty, Layer.DEMAND)
                val atOrBelow = k >= path.size - 1
                assertEquals(!atOrBelow, ops.filter(cut, f) != null, "$name cut@$k")
            }
            // primitive-tracking mark: kept everywhere.
            assertTrue(ops.filter(manager.factsOf(fact(path, Tail.EXACT, tracked), ExclusionSet.Empty, layer), f) != null, "$name $layer tracked")
        }
    }

    /** Assumption A1: the candidate marks are all marks of the subtree at the first boxed level. One fact with leaves at
     *  `[e]^k` (T and T%%primitive%%), `[e]^k.value` (U and %%primitive%%, the exact tail) and a sibling field
     *  `[e]^k.sibling` (V, an any tail), and for an array a root leaf W above the boxed level. Each ordinary mark sits
     *  on one leaf only. The filter removes every ordinary mark at and below the boxed level, keeps both
     *  primitive-tracking marks and W, and agrees with the per-path reference on every leaf. */
    @Test
    fun `G6 drop form - one multi-leaf fact per boxed type loses every ordinary mark below the boxed level`(): Unit {
        val t = ordinary
        val u = manager.marks.mark("U")
        val v = manager.marks.mark("V")
        val w = manager.marks.mark("W")
        val primitive = manager.marks.mark("%%primitive%%")
        val boxedValue = mapOf(
            "java.lang.Integer" to "int", "java.lang.Character" to "char", "java.lang.Long" to "long", "java.lang.Boolean" to "boolean")
        val alg = manager.taintAlg
        val e = manager.accessors.index(ElementAccessor)
        fun leaves(exact: List<TaintMark>, any: List<TaintMark> = emptyList()) =
            manager.taintLeaves(MarkSet(exact.map { it.id }.toIntArray()), MarkSet(any.map { it.id }.toIntArray()))
        fun node(leaf: TaintLeaves, children: Map<Int, TaintNode>): TaintNode {
            val sorted = children.toSortedMap()
            return alg.node(leaf, sorted.keys.toIntArray(), sorted.values.toTypedArray())
        }
        for (name in types.filter { levels(it).last() in boxedTypes }) for (layer in listOf(Layer.NORMAL, Layer.DEMAND)) {
            val boxedClass = levels(name).last()
            val k = levels(name).size - 1
            val value = manager.accessors.index(FieldAccessor(boxedClass, "value", boxedValue.getValue(boxedClass)))
            val sibling = manager.accessors.index(FieldAccessor(boxedClass, "sibling", "java.lang.Object"))
            var root = node(leaves(listOf(t, tracked)), mapOf(
                value to alg.leafNode(leaves(listOf(u, primitive))),
                sibling to alg.leafNode(leaves(emptyList(), any = listOf(v))),
            ))
            repeat(k) { level -> root = node(if (level == k - 1) leaves(listOf(w)) else TaintLeaves.EMPTY, mapOf(e to root)) }
            val input = manager.taintTree(x, layer, root)
            val f = filter(name)
            val output = ops.filter(input, f)
            val spine = List(k) { e }
            fun named(patterns: Sequence<Pattern>) = patterns.map { p ->
                p.fact.path to manager.marks.name((p.fact.mark as MarkSlot.Concrete).mark)
            }.toSet()
            val expected = setOfNotNull(
                if (k > 0) emptyList<Int>() to "W" else null,
                spine to "T%%primitive%%",
                spine + value to "%%primitive%%",
            )
            val inputLeaves = ops.leaves(input).toList()
            assertEquals(5 + (if (k > 0) 1 else 0), inputLeaves.size, "$name $layer input leaves")
            assertEquals(expected, output?.let { named(ops.leaves(it)) }.orEmpty(), "$name $layer")
            // The runtime filter of the whole fact equals the per-path reference on each of its leaves.
            val kept = output?.let { named(ops.leaves(it)) }.orEmpty()
            for (leaf in inputLeaves) {
                val c = Conclusion(leaf.fact, leaf.exclusion, layer == Layer.DEMAND)
                assertEquals(reference.passes(f, c), named(sequenceOf(leaf)).single() in kept, "$name $layer ${leaf.fact}")
            }
        }
    }
}

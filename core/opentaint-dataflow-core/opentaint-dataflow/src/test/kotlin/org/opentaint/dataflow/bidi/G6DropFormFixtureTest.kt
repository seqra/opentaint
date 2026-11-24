package org.opentaint.dataflow.bidi

import org.junit.jupiter.api.Test
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ElementAccessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FactTypeChecker.FilterResult
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.bidi.ap.*
import org.opentaint.dataflow.bidi.ap.ExclusionSet
import org.opentaint.dataflow.bidi.driver.*
import org.opentaint.dataflow.bidi.engine.*
import org.opentaint.dataflow.bidi.fixtures.*
import org.opentaint.dataflow.bidi.interp.*
import org.opentaint.dataflow.bidi.interp.CallPoint.*
import org.opentaint.dataflow.bidi.interp.StageKind.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

/**
 * G6 drop form (spec/acyclic-group-a-implementation.md §3, R1) on analysis fixtures: at and below a boxed spine level
 * (a class that unboxes to a primitive) the type filter's mark policy removes an ordinary mark from the whole value,
 * field leaves included. The programs come from DecidedStopAttackTest M4 (proto/dt-owner-cover-20261124) and from
 * DeepChainFixtureTest D5/D6 and StringChainFixtureTest (proto/g6-drop-xsub-20261120); the stop-policy checks of those
 * tests are not ported. Expectations: docs/reports/g6-drop-xsub-20261120.md §5.1.
 *
 * Each program has a carrier sink A (x has T anywhere | s has T): A is confirmed at run 1 through the shallow s, and
 * the deep source x keeps A DEMAND-reached until the field limit K covers it. Sink B needs the mark below a boxed value.
 * Each variant runs the production driver once (IncreasingLimits, run-1 mark mode FULL) and reads the final report
 * and, per complete forward barrier, L (the reached sink rules) and C (the root ZERO NormalTargets so far).
 *
 * - M4, D5, D6 (`policy = true`) and the 13 String-chain variants with an ordinary mark below an Integer: B is found at
 *   no K. The policy drops T on the boxed value, on the exact `value` leaf as on every K-cut of it.
 * - Controls (`policy = false`, every other String-chain variant, among them the callee case that loses B through the
 *   run-1 drop of B's sink seed): unchanged.
 */
class G6DropFormFixtureTest {
    data class Barrier(val run: Int, val k: Int, val reached: Set<String>, val confirmed: Set<String>)

    class Outcome(val barriers: List<Barrier>, val report: Report) {
        val published: Set<String> get() = report.entries.mapTo(sortedSetOf()) { (if (it.provisional) "P:" else "") + it.descriptor.key.ruleId }
        val end: String get() = "${report.end.reason}@${report.end.run}"
        val reachedB: Set<Int> get() = barriers.filter { "B" in it.reached }.mapTo(sortedSetOf()) { it.run }
        val confirmedB: Int? get() = barriers.firstOrNull { "B" in it.confirmed }?.run
        fun render(): String = barriers.joinToString("\n") {
            "  run=${it.run} K=${it.k} L=${it.reached.sorted()} C=${it.confirmed.sorted()}"
        } + "\n  end=$end published=$published"
    }

    companion object {
        /** Forward run index r has field limit K = 1 (r = 1) or r - 1: the first forward run with K >= depth. */
        fun firstRunWithLimit(depth: Int): Int = if (depth <= 1) 1 else if (depth % 2 == 0) depth + 1 else depth + 2
        private fun odd(from: Int, to: Int): Set<Int> = (from..to step 2).toSet()
        private fun fieldLimit(run: Int): Int = if (run == 1) 1 else run - 1
    }

    /** The production driver without a stop policy; its stdout is kept only with G6_FIXTURE_LOG=true. */
    private fun analyze(f: DriverFixtures, roots: List<MethodKey>, cutoff: Int): Outcome {
        val driver = f.driver(HardRunLimitPolicy(IncreasingLimits, cutoff), budget = 60.seconds, run1MarkMode = MarkMode.FULL)
        val out = System.out
        val captured = java.io.ByteArrayOutputStream()
        System.setOut(java.io.PrintStream(captured, true))
        val report = try { driver.analyze(roots) } finally { System.setOut(out) }
        if (System.getenv("G6_FIXTURE_LOG") == "true") print(captured.toString())
        val confirmed = LinkedHashSet<String>()
        val barriers = ArrayList<Barrier>()
        for ((config, result) in f.configs.zip(f.results)) {
            if (config.direction != Direction.FORWARD || result.status != RunStatus.COMPLETE) continue
            if (config.index > report.end.run) continue
            val reached = LinkedHashSet<String>()
            for (actor in result.analyzers) {
                for (id in actor.reachedSinkReportIds) reached += f.shared.reportCatalog.descriptor(id).key.ruleId
                if (actor.key !in roots) continue
                for (row in actor.targets) {
                    val target = row.target as? Target.NormalTarget ?: continue
                    if (row.premise.isZero) confirmed += f.shared.reportCatalog.descriptor(target.id).key.ruleId
                }
            }
            barriers += Barrier(config.index, config.fieldLimit, reached, LinkedHashSet(confirmed))
        }
        return Outcome(barriers, report)
    }

    /** Runs every variant and fails once at the end with all variant failures. */
    private class Variants {
        val failures = ArrayList<String>()
        fun variant(name: String, body: () -> Unit) {
            runCatching(body).onFailure { failures += "$name: ${it.message}" }
        }
    }

    private fun allVariants(body: Variants.() -> Unit) {
        val v = Variants().apply(body)
        assertTrue(v.failures.isEmpty(), "${v.failures.size} variants failed:\n" + v.failures.joinToString("\n\n"))
    }

    private fun acceptAll() = object : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor) = FilterResult.Accept
    }

    /** The filter of a value of type Integer[]^levels, as JIRTypeFilters.make builds it: only the Integer level is
     *  primitive, and it is boxed; T is not primitive-tracking. */
    private fun boxedFilter(levels: Int): TypeFilter = TypeFilter(acceptAll(), LevelMarkPolicy(
        BooleanArray(levels + 1) { it == levels }, BooleanArray(levels + 1) { it == levels }, primitiveTracking = { false }))

    // ---------------------------------------------------------------------------------------------------------------
    // M4 (DecidedStopAttackTest). x: Integer[]^levels holds T at x.[e]^levels.value. An operand use of x applies the
    // filter of Integer[]^levels; then y = x.[e]^levels.value and B(y). The K-cut x.[e]^levels.[any] and the exact
    // x.[e]^levels.value lose T alike: B is found at no K. policy = false is the control without the filter.

    @Test
    fun `M4 a boxed array element loses an ordinary mark at every field limit`() {
        allVariants { for (levels in listOf(1, 2)) for (policy in listOf(false, true)) variant("M4 levels=$levels policy=$policy") { m4(levels, policy) } }
    }

    private fun m4(levels: Int, policy: Boolean) = DriverFixtures().use { f ->
        val p = f.program
        val root = p.method("main", List(5) { if (it == 4) emptyList() else listOf(it + 1) }, 4).key()
        val x = AccessPathBase.LocalVar(0); val y = AccessPathBase.LocalVar(1); val s = AccessPathBase.LocalVar(2)
        val a0 = AccessPathBase.Argument(0); val a1 = AccessPathBase.Argument(1)
        val t = p.mark("T"); val mark = MarkSlot.Concrete(t)
        val path = List(levels) { ELEMENT_ACCESSOR_IDX } + p.field("value")
        p.entry(root, RuleStatement(f.summary(ZERO_KEEP,
            PathEdge(ZERO_FACT, PathFact(x, path, Tail.EXACT, mark), ExclusionSet.Empty),
            PathEdge(ZERO_FACT, PathFact(s, emptyList(), Tail.EXACT, mark), ExclusionSet.Empty)), StatementSummary.EMPTY, emptyList()))
        // 1: sink A(x has T anywhere | s has T): confirmed through s, DEMAND-reached through x.
        val sinkA = listOf(SinkRule(f.rule("A"), 0, listOf(p.pattern(a0, tail = Tail.ANY, mark = mark)), emptyList()),
            SinkRule(f.rule("A"), 1, listOf(p.pattern(a1, mark = mark)), emptyList()))
        p.call(root, 1, CallPlan(setOf(x, s), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(x, emptyList(), a0, emptyList()), starEdge(s, emptyList(), a1, emptyList()))),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(ZERO_KEEP, keepEdge(a0), keepEdge(a1))),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(a0, emptyList(), x, emptyList()), starEdge(a1, emptyList(), s, emptyList())))),
            sinkA, BEFORE, AFTER))
        // 2: an operand use of x: Integer[]^levels.
        p.statement(root, 2, MicroEdgeBuilder().apply { keep(x); if (policy) operandFilter(x, boxedFilter(levels)) }.build())
        // 3: y = x[e]^levels.value; 4: exit sink B(y has T)
        p.statement(root, 3, MicroEdgeBuilder().apply { read(y, x, path) }.build())
        p.exit(root, 4, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(SinkRule(f.rule("B"), 0, listOf(p.pattern(y, mark = mark)), emptyList()))), false, emptySet()))
        val o = analyze(f, listOf(root), cutoff = 21)
        println("G6_FIXTURE M4 levels=$levels policy=$policy\n${o.render()}")
        val where = "M4 levels=$levels policy=$policy\n${o.render()}"
        assertEquals(if (policy) setOf("A") else setOf("A", "B"), o.published, where)
        assertEquals(EndReason.NO_DEMAND_EDGE, o.report.end.reason, where)
        assertEquals(2 * levels + 1, o.report.end.run, where)
        assertTrue(o.report.entries.none { it.provisional }, where)
    }

    // ---------------------------------------------------------------------------------------------------------------
    // D5, D6 (DeepChainFixtureTest). A deep field chain that ends inside a boxed value. Source T on
    // x.f1..fp.[e]^levels.value; y = x.f1..fp (static type Integer[]^levels, Integer when levels = 0); an operand use of
    // y applies its type filter; z = y.[e]^levels.value; B(z). The cut at K puts T on an ANY leaf at depth K of x. With
    // the policy, the Integer level of y loses T on the whole value, also on the exact y.[e]^levels.value: B is found at
    // no K. B stays in L only while the cut leaf is above the boxed level (K < prefix + levels, D6). policy = false is
    // the control without the filter.

    /** [end]: the run of the NO_DEMAND_EDGE end. [confirm]: the run that confirms B (null: never). [reachedB]: the
     *  forward runs whose L contains B. */
    data class DeepExpect(val end: Int, val confirm: Int?, val reachedB: Set<Int>)

    @Test
    fun `D5 boxed value below a deep field chain loses an ordinary mark at every field limit`() {
        allVariants {
            for (prefix in 1..6) for (policy in listOf(true, false)) {
                val end = firstRunWithLimit(prefix + 1)
                val expect = if (policy) DeepExpect(end, null, emptySet()) else DeepExpect(end, end, odd(1, end))
                variant("D5 boxed value prefix=$prefix policy=$policy") { deep(expect) { boxed(it, prefix, 0, policy) } }
            }
        }
    }

    @Test
    fun `D6 boxed element chain below a deep field chain loses an ordinary mark at every field limit`() {
        allVariants {
            for (prefix in 0..7) for (levels in 1..2) for (policy in listOf(true, false)) {
                val end = firstRunWithLimit(prefix + levels + 1)
                val expect = if (policy) DeepExpect(end, null, odd(1, end).filterTo(sortedSetOf()) { fieldLimit(it) < prefix + levels })
                    else DeepExpect(end, end, odd(1, end))
                variant("D6 boxed elements prefix=$prefix levels=$levels policy=$policy") { deep(expect) { boxed(it, prefix, levels, policy) } }
            }
        }
    }

    private fun deep(expect: DeepExpect, build: (DriverFixtures) -> List<MethodKey>) = DriverFixtures().use { f ->
        val o = analyze(f, build(f), cutoff = 31)
        val where = o.render()
        assertEquals(RunStatus.COMPLETE, o.report.end.status, where)
        assertEquals(EndReason.NO_DEMAND_EDGE, o.report.end.reason, where)
        assertEquals(expect.end, o.report.end.run, where)
        assertEquals(if (expect.confirm != null) setOf("A", "B") else setOf("A"), o.published, where)
        assertEquals(expect.confirm, o.confirmedB, where)
        assertTrue(o.barriers.all { "A" in it.confirmed }, where)
        assertEquals(expect.reachedB, o.reachedB, where)
    }

    private fun boxed(f: DriverFixtures, prefix: Int, levels: Int, policy: Boolean): List<MethodKey> {
        val p = f.program
        val mark = MarkSlot.Concrete(p.mark("T"))
        val a0 = AccessPathBase.Argument(0); val a1 = AccessPathBase.Argument(1)
        fun source(b: AccessPathBase, path: List<Int> = emptyList()) = PathEdge(ZERO_FACT, PathFact(b, path, Tail.EXACT, mark), ExclusionSet.Empty)
        val root = p.method("main", List(6) { if (it == 5) emptyList() else listOf(it + 1) }, 5).key()
        val x = AccessPathBase.LocalVar(0); val y = AccessPathBase.LocalVar(1); val s = AccessPathBase.LocalVar(2); val z = AccessPathBase.LocalVar(3)
        val pre = (1..prefix).map { p.field("f$it") }
        val tail = List(levels) { ELEMENT_ACCESSOR_IDX } + p.field("value")
        p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source(x, pre + tail), source(s)), StatementSummary.EMPTY, emptyList()))
        // 1: carrier A(x has T anywhere | s has T).
        val sinkA = listOf(SinkRule(f.rule("A"), 0, listOf(p.pattern(a0, tail = Tail.ANY, mark = mark)), emptyList()),
            SinkRule(f.rule("A"), 1, listOf(p.pattern(a1, mark = mark)), emptyList()))
        p.call(root, 1, CallPlan(setOf(x, s), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(x, emptyList(), a0, emptyList()), starEdge(s, emptyList(), a1, emptyList()))),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(ZERO_KEEP, keepEdge(a0), keepEdge(a1))),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(a0, emptyList(), x, emptyList()), starEdge(a1, emptyList(), s, emptyList())))),
            sinkA, BEFORE, AFTER))
        // 2: y = x.f1..fp; 3: an operand use of y: Integer[]^levels; 4: z = y.[e]^levels.value; 5: exit sink B(z).
        p.statement(root, 2, MicroEdgeBuilder().apply { if (prefix > 0) read(y, x, pre) else move(y, x) }.build())
        p.statement(root, 3, MicroEdgeBuilder().apply { keep(y); if (policy) operandFilter(y, boxedFilter(levels)) }.build())
        p.statement(root, 4, MicroEdgeBuilder().apply { read(z, y, tail) }.build())
        p.exit(root, 5, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(SinkRule(f.rule("B"), 0, listOf(p.pattern(z, emptyList(), Tail.EXACT, mark)), emptyList()))), false, emptySet()))
        return listOf(root)
    }

    // ---------------------------------------------------------------------------------------------------------------
    // String chains (StringChainFixtureTest). Program shape (as D5): entry x.f1..fp.<holderPath> := T and s := T;
    // carrier A; y = x.f1..fp (the holder); an operand use of y with the type filter of its static type; optional steps
    // (field and array reads with the result filter of the read type, a collection get, a cast); exit sink B on the last
    // value. The type filters are [ModelType], a replica of the production filter (JIRTypeFilters.make);
    // JIRStringChainFiltersTest (opentaint-jvm-dataflow) checks that real JIR types give the same decision rows.

    /** A fixture accessor: the production accessors of String, Integer, the collection models, and a user class. */
    enum class Acc(val accessor: Accessor) {
        S_VALUE(FieldAccessor("java.lang.String", "value", "byte[]")),
        S_CODER(FieldAccessor("java.lang.String", "coder", "byte")),
        S_HASH(FieldAccessor("java.lang.String", "hash", "int")),
        I_VALUE(FieldAccessor("java.lang.Integer", "value", "int")),
        E(ElementAccessor),
        LIST_ELEMENT(FieldAccessor("java.lang.Iterable", "Element", "java.lang.Object")),
        MAP_VALUE(FieldAccessor("java.util.Map", "MapValue", "java.lang.Object")),
        BOX_VALUE(FieldAccessor("Box", "value", "Box")),
    }

    /**
     * Replica of JIRTypeFilters.make for one static type:
     * - `may` follows JIRFactTypeChecker.AccessorFilter: a field passes on a reference type whose class may be a subtype
     *   or supertype of the declaring class ([owners]; null = every class); an element passes on an array (FilterNext
     *   with the element type) or on Object; a primitive rejects both; other accessors pass. It reads edges only.
     * - the mark policy is LevelMarkPolicy over the element levels: primitive = a primitive, a boxed class or
     *   Character; boxed = such a level that is a class; null if no level is primitive. Primitive tracking = the mark
     *   name ends with "%%primitive%%" (JIRTypeFilters.isPrimitiveTracking).
     */
    class ModelType private constructor(
        val name: String, private val ref: Boolean, private val owners: Set<String>?, val element: ModelType?,
        private val objectRoot: Boolean, val primitive: Boolean, val boxed: Boolean,
    ) : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FilterResult = when (accessor) {
            is FieldAccessor -> if (ref && (owners == null || accessor.className in owners)) FilterResult.Accept else FilterResult.Reject
            ElementAccessor -> when {
                !ref -> FilterResult.Reject
                element != null -> FilterResult.FilterNext(element)
                objectRoot -> FilterResult.Accept
                else -> FilterResult.Reject
            }
            else -> FilterResult.Accept
        }

        fun levels(): List<ModelType> = generateSequence(this) { it.element }.toList()

        fun filter(m: ApManager): TypeFilter {
            val levels = levels()
            val primitive = levels.map { it.primitive }
            return TypeFilter(this, if (true !in primitive) null else LevelMarkPolicy(primitive.toBooleanArray(),
                levels.map { it.boxed }.toBooleanArray(), { m.marks.name(it).endsWith(PRIMITIVE_SUFFIX) }))
        }

        /** The decision row that JIRStringChainFiltersTest compares with real JIR types. */
        fun signature(): String = Acc.entries.joinToString(" ") { a ->
            "${a.name}=" + when (val r = check(a.accessor)) {
                FilterResult.Accept -> "A"
                FilterResult.Reject -> "R"
                is FilterResult.FilterNext -> "N:${(r.filter as ModelType).name}"
            }
        } + " policy=" + levels().let { l -> if (l.none { it.primitive }) "null"
            else l.joinToString(",") { if (it.boxed) "boxed" else if (it.primitive) "prim" else "-" } }

        override fun toString(): String = name

        companion object {
            const val PRIMITIVE_SUFFIX = "%%primitive%%"
            private fun prim(name: String) = ModelType(name, false, emptySet(), null, false, primitive = true, boxed = false)
            val BYTE = prim("byte")
            val CHAR = prim("char")
            val INT = prim("int")
            val INTEGER = ModelType("java.lang.Integer", true, setOf("java.lang.Integer", "java.lang.Number"), null, false, primitive = true, boxed = true)
            val NUMBER = ModelType("java.lang.Number", true, setOf("java.lang.Number", "java.lang.Integer"), null, false, false, false)
            val STRING = ModelType("java.lang.String", true, setOf("java.lang.String"), null, false, false, false)
            val OBJECT = ModelType("java.lang.Object", true, null, null, true, false, false)
            val LIST = ModelType("java.util.List", true, setOf("java.lang.Iterable"), null, false, false, false)
            val MAP = ModelType("java.util.Map", true, setOf("java.util.Map"), null, false, false, false)
            val BOX = ModelType("Box", true, setOf("Box"), null, false, false, false)
            fun array(e: ModelType, dims: Int = 1): ModelType =
                if (dims == 0) e else ModelType(array(e, dims - 1).name + "[]", true, emptySet(), array(e, dims - 1), false, false, false)
        }
    }

    sealed interface Step {
        /** An operand use of the current value with the filter of its static type (D5 statement 3). */
        data class Use(val type: ModelType) : Step
        /** next = current.path; operand filter of the current type, result filter of [type] (null: none, as D5). */
        data class Read(val path: List<Acc>, val type: ModelType?) : Step
        /** next = get(current) of a List/Map model. [callee] = false: an unresolved call with the pass-through rule
         *  this.field -> result as UNRESOLVED call-site edges; true: a callee method get(a0) { return a0.field }. */
        data class Get(val field: Acc, val callee: Boolean) : Step
        /** next = (type) current: operand filter and result filter of [type]. */
        data class Cast(val type: ModelType) : Step
    }

    /** [confirm]: the run that confirms B (null: never). [losesB]: an ordinary mark below an Integer that the analysis
     *  needs to confirm B: B is found at no K and is never reached. */
    data class Variant(val name: String, val prefix: Int, val holderPath: List<Acc>, val steps: List<Step>,
                       val sinkPath: List<Acc>, val sinkAny: Boolean = false, val tracked: Boolean = false,
                       val confirm: Int?, val losesB: Boolean = false)

    private val tracked = "T%%primitive%%"
    private val declarations: MarkDeclarations = fixtureMarkDeclarations(COMMON_FIXTURE_MARK_NAMES + tracked)
    private val rows = java.util.concurrent.ConcurrentLinkedQueue<String>()

    private fun build(f: DriverFixtures, v: Variant): List<MethodKey> {
        val p = f.program
        val ap = f.shared.ap
        fun idx(a: Acc) = ap.accessors.index(a.accessor)
        fun idx(path: List<Acc>) = path.map(::idx)
        val mark = MarkSlot.Concrete(p.mark(if (v.tracked) tracked else "T"))
        val a0 = AccessPathBase.Argument(0)
        val a1 = AccessPathBase.Argument(1)
        val ret = AccessPathBase.Return
        val n = 3 + v.steps.size
        val root = p.method("main", List(n + 1) { if (it == n) emptyList() else listOf(it + 1) }, n).key()
        val x = AccessPathBase.LocalVar(0); val s = AccessPathBase.LocalVar(1); val y = AccessPathBase.LocalVar(2)
        val pre = (1..v.prefix).map { p.field("f$it") }
        fun source(b: AccessPathBase, path: List<Int>) = PathEdge(ZERO_FACT, PathFact(b, path, Tail.EXACT, mark), ExclusionSet.Empty)
        p.entry(root, RuleStatement(f.summary(ZERO_KEEP, source(x, pre + idx(v.holderPath)), source(s, emptyList())),
            StatementSummary.EMPTY, emptyList()))
        // 1: carrier A(x has T anywhere | s has T): confirmed at run 1 through s, DEMAND-reached through x.
        val sinkA = listOf(SinkRule(f.rule("A"), 0, listOf(p.pattern(a0, tail = Tail.ANY, mark = mark)), emptyList()),
            SinkRule(f.rule("A"), 1, listOf(p.pattern(a1, mark = mark)), emptyList()))
        p.call(root, 1, CallPlan(setOf(x, s), listOf(
            CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(x, emptyList(), a0, emptyList()), starEdge(s, emptyList(), a1, emptyList()))),
            CallStage.Actions(BOUND, ADDED, emptyList()),
            CallStage.Edges(ADDED, RETURNED, UNRESOLVED, f.summary(ZERO_KEEP, keepEdge(a0), keepEdge(a1))),
            CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
            CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(a0, emptyList(), x, emptyList()), starEdge(a1, emptyList(), s, emptyList())))),
            sinkA, BEFORE, AFTER))
        // 2: y = x.f1..fp (no filter, as D5).
        p.statement(root, 2, MicroEdgeBuilder().apply { if (v.prefix > 0) read(y, x, pre) else move(y, x) }.build())
        var cur = y
        var type: ModelType? = null
        for ((i, step) in v.steps.withIndex()) {
            val index = 3 + i
            val next = AccessPathBase.LocalVar(10 + i)
            when (step) {
                is Step.Use -> {
                    p.statement(root, index, MicroEdgeBuilder().apply { keep(cur); operandFilter(cur, step.type.filter(ap)) }.build())
                    type = step.type
                    continue
                }
                is Step.Read -> p.statement(root, index, MicroEdgeBuilder().apply {
                    read(next, cur, idx(step.path))
                    operandFilter(cur, type?.filter(ap))
                    resultFilter(next, step.type?.filter(ap))
                }.build()).also { type = step.type }
                is Step.Get -> {
                    val call = if (step.callee) {
                        val get = p.method("get$i", listOf(listOf(1), listOf(2), emptyList()), 2).key()
                        p.statement(get, 1, MicroEdgeBuilder().apply { read(ret, a0, listOf(idx(step.field))) }.build())
                        CallStage.Callees(ADDED, RETURNED, listOf(get))
                    } else CallStage.Edges(ADDED, RETURNED, UNRESOLVED,
                        f.summary(ZERO_KEEP, keepEdge(a0), starEdge(a0, listOf(idx(step.field)), ret, emptyList())))
                    p.call(root, index, CallPlan(setOf(cur, next), listOf(
                        CallStage.Edges(BEFORE, BOUND, BIND_IN, f.summary(ZERO_KEEP, starEdge(cur, emptyList(), a0, emptyList()))),
                        CallStage.Actions(BOUND, ADDED, emptyList()),
                        call,
                        CallStage.Actions(RETURNED, REWRITTEN, emptyList()),
                        CallStage.Edges(REWRITTEN, AFTER, BIND_BACK, f.summary(ZERO_KEEP, starEdge(a0, emptyList(), cur, emptyList()),
                            starEdge(ret, emptyList(), next, emptyList())))),
                        emptyList(), BEFORE, AFTER))
                    type = ModelType.OBJECT
                }
                is Step.Cast -> p.statement(root, index, MicroEdgeBuilder().apply {
                    move(next, cur)
                    operandFilter(cur, step.type.filter(ap))
                    resultFilter(next, step.type.filter(ap))
                }.build()).also { type = step.type }
            }
            cur = next
        }
        p.exit(root, n, ExitRules(RuleStatement(StatementSummary.EMPTY, StatementSummary.EMPTY,
            listOf(SinkRule(f.rule("B"), 0, listOf(p.pattern(cur, idx(v.sinkPath), if (v.sinkAny) Tail.ANY else Tail.EXACT, mark)),
                emptyList()))), false, emptySet()))
        return listOf(root)
    }

    /** Runs one variant; returns null or the failure text. */
    private fun check(v: Variant): String? = DriverFixtures(markDeclarations = declarations).use { f ->
        val o = analyze(f, build(f, v), cutoff = 31)
        rows += "G6_FIXTURE_ROW | ${v.name} | ${o.end} | ${o.published} | ${o.reachedB.joinToString(",").ifEmpty { "-" }} | ${o.confirmedB ?: "never"} |"
        val failures = ArrayList<String>()
        fun need(ok: Boolean, what: String) { if (!ok) failures += what }
        need(o.report.end.status == RunStatus.COMPLETE, "status ${o.report.end.status}")
        need(o.barriers.all { "A" in it.confirmed }, "A is not confirmed at every barrier")
        need(o.published == (if (v.confirm != null) setOf("A", "B") else setOf("A")), "report ${o.published}")
        need(o.confirmedB == v.confirm, "B confirmed at ${o.confirmedB}, expected ${v.confirm}")
        if (v.losesB) {
            // The analysis ends when the carrier's deep source is exact (K >= prefix + holder depth); B is never reached.
            val end = firstRunWithLimit(v.prefix + v.holderPath.size)
            need(o.report.end.reason == EndReason.NO_DEMAND_EDGE && o.report.end.run == end, "end ${o.end}, expected NO_DEMAND_EDGE@$end")
            need(o.reachedB.isEmpty(), "B is reached at ${o.reachedB}")
        }
        if (failures.isEmpty()) null else "${v.name}: ${failures.joinToString("; ")}\n${o.render()}"
    }

    private fun run(variants: List<Variant>) {
        rows.clear()
        val failures = variants.mapNotNull(::check)
        rows.forEach(::println)
        assertTrue(failures.isEmpty(), "${failures.size} of ${variants.size} variants failed:\n" + failures.joinToString("\n\n"))
    }

    private fun use(t: ModelType) = Step.Use(t)
    private fun read(t: ModelType?, vararg path: Acc) = Step.Read(path.toList(), t)
    private fun marks() = listOf(false, true)
    private fun tag(tracked: Boolean) = if (tracked) "mark=T%%primitive%%" else "mark=T"
    private fun fr(depth: Int) = firstRunWithLimit(depth)

    @Test
    fun `model type filters have the production decision rows`() {
        val expected = mapOf(
            ModelType.STRING to "S_VALUE=A S_CODER=A S_HASH=A I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            ModelType.array(ModelType.STRING) to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:java.lang.String LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            ModelType.array(ModelType.STRING, 2) to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:java.lang.String[] LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            ModelType.INTEGER to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=A E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=boxed",
            ModelType.NUMBER to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=A E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=null",
            ModelType.OBJECT to "S_VALUE=A S_CODER=A S_HASH=A I_VALUE=A E=A LIST_ELEMENT=A MAP_VALUE=A BOX_VALUE=A policy=null",
            ModelType.LIST to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=A MAP_VALUE=R BOX_VALUE=R policy=null",
            ModelType.MAP to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=A BOX_VALUE=R policy=null",
            ModelType.INT to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=prim",
            ModelType.array(ModelType.INT) to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:int LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,prim",
            ModelType.array(ModelType.BYTE) to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:byte LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,prim",
            ModelType.array(ModelType.CHAR) to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:char LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,prim",
            ModelType.array(ModelType.INTEGER) to "S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=N:java.lang.Integer LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=R policy=-,boxed",
        )
        for ((type, row) in expected) assertEquals(row, type.signature(), type.name)
        // The user class: its own fields pass, no policy (JIR: a sample class, JIRStringChainFiltersTest).
        assertEquals("S_VALUE=R S_CODER=R S_HASH=R I_VALUE=R E=R LIST_ELEMENT=R MAP_VALUE=R BOX_VALUE=A policy=null", ModelType.BOX.signature())
    }

    // S. String holder at the end of a deep field chain. The String filter has no mark policy. Reads into a
    // byte/int/byte[] element apply the true primitive policy to the exact fact and to the cut alike.

    @Test
    fun `S String holder below a deep field chain is unchanged`() {
        val s = ModelType.STRING
        val bytes = ModelType.array(ModelType.BYTE)
        val variants = ArrayList<Variant>()
        for (prefix in listOf(1, 2, 4)) for (tracked in marks()) {
            fun v(name: String, holder: List<Acc>, steps: List<Step>, sink: List<Acc>, depth: Int, ordinaryConfirms: Boolean = true, any: Boolean = false) {
                val confirm = if (ordinaryConfirms || tracked) fr(prefix + depth) else null
                variants += Variant("S $name prefix=$prefix ${tag(tracked)}", prefix, holder, listOf(use(s)) + steps, sink, any, tracked, confirm)
            }
            v("T on the String, B(y)", emptyList(), emptyList(), emptyList(), 0)
            v("T on value, B(y.value)", listOf(Acc.S_VALUE), emptyList(), listOf(Acc.S_VALUE), 1)
            v("T on value, z = y.value: byte[], B(z)", listOf(Acc.S_VALUE), listOf(read(bytes, Acc.S_VALUE)), emptyList(), 1)
            v("T on coder, B(y.coder)", listOf(Acc.S_CODER), emptyList(), listOf(Acc.S_CODER), 1)
            v("T on coder, z = y.coder: byte, B(z)", listOf(Acc.S_CODER), listOf(read(ModelType.BYTE, Acc.S_CODER)), emptyList(), 1, ordinaryConfirms = false)
            v("T on hash, B(y.hash)", listOf(Acc.S_HASH), emptyList(), listOf(Acc.S_HASH), 1)
            v("T on hash, z = y.hash: int, B(z)", listOf(Acc.S_HASH), listOf(read(ModelType.INT, Acc.S_HASH)), emptyList(), 1, ordinaryConfirms = false)
            v("T on value[e], B(y.value[e])", listOf(Acc.S_VALUE, Acc.E), emptyList(), listOf(Acc.S_VALUE, Acc.E), 2)
            v("T on value[e], z = y.value: byte[], B(z[e])", listOf(Acc.S_VALUE, Acc.E), listOf(read(bytes, Acc.S_VALUE)), listOf(Acc.E), 2, ordinaryConfirms = false)
            v("T on value[e], z = y.value, w = z[e]: byte, B(w)", listOf(Acc.S_VALUE, Acc.E),
                listOf(read(bytes, Acc.S_VALUE), read(ModelType.BYTE, Acc.E)), emptyList(), 2, ordinaryConfirms = false)
            v("T on value[e], B(y has T anywhere)", listOf(Acc.S_VALUE, Acc.E), emptyList(), emptyList(), 2, any = true)
        }
        run(variants)
    }

    // SA. String[]^l holder (l = 1, 2): the cut leaf at depth K = p + l sits at element level l of y, the String level.
    // The String[]^l filter has no mark policy.

    @Test
    fun `SA String array holder below a deep field chain is unchanged`() {
        val variants = ArrayList<Variant>()
        for (levels in 1..2) for (prefix in 0..4) {
            val holder = ModelType.array(ModelType.STRING, levels)
            val elements = List(levels) { Acc.E }
            val reads = (1..levels).map { k -> read(ModelType.array(ModelType.STRING, levels - k), Acc.E) }
            val base = "SA String[]^$levels prefix=$prefix"
            variants += Variant("$base T on the elements, B(y[e]^l)", prefix, elements, listOf(use(holder)), elements, confirm = fr(prefix + levels))
            variants += Variant("$base T on the elements, z = y[e]^l: String, B(z)", prefix, elements, listOf(use(holder)) + reads, emptyList(),
                confirm = fr(prefix + levels))
            variants += Variant("$base T on element value, B(y[e]^l.value)", prefix, elements + Acc.S_VALUE, listOf(use(holder)),
                elements + Acc.S_VALUE, confirm = fr(prefix + levels + 1))
            variants += Variant("$base T on element value, z = y[e]^l, B(z.value)", prefix, elements + Acc.S_VALUE, listOf(use(holder)) + reads,
                listOf(Acc.S_VALUE), confirm = fr(prefix + levels + 1))
        }
        run(variants)
    }

    // C. Element of a List or Map model at the end of a deep field chain: y = x.f1..fp (List/Map), r = get(y),
    // v = (String) r or (Integer) r, sink on v. get is the pass-through rule this.Element -> result (this.MapValue for
    // Map) at an unresolved call, or a callee method with the same body. The (Integer) cast with an ordinary mark: B
    // is found at no K in both forms. With the callee, the run-1 policy drop removes B's DEMAND witness, so B has no
    // sink seed, the callee gets no demand rows in the restricted runs, and B is never reached.

    @Test
    fun `C String and Integer in List and Map models - the Integer cast drops an ordinary mark`() {
        val variants = ArrayList<Variant>()
        for ((container, field) in listOf(ModelType.LIST to Acc.LIST_ELEMENT, ModelType.MAP to Acc.MAP_VALUE))
            for (callee in listOf(false, true)) for (prefix in listOf(1, 3)) {
                val base = "C ${container.name.substringAfterLast('.')} get=${if (callee) "callee" else "rule"} prefix=$prefix"
                fun steps(t: ModelType) = listOf(use(container), Step.Get(field, callee), Step.Cast(t))
                variants += Variant("$base (String) get, T on the element, B(v)", prefix, listOf(field), steps(ModelType.STRING), emptyList(),
                    confirm = fr(prefix + 1))
                variants += Variant("$base (String) get, T on element value, B(v.value)", prefix, listOf(field, Acc.S_VALUE),
                    steps(ModelType.STRING), listOf(Acc.S_VALUE), confirm = fr(prefix + 2))
                for (tracked in marks()) variants += Variant("$base (Integer) get, T on element value, B(v.value) ${tag(tracked)}", prefix,
                    listOf(field, Acc.I_VALUE), steps(ModelType.INTEGER), listOf(Acc.I_VALUE), tracked = tracked,
                    confirm = if (tracked) fr(prefix + 2) else null, losesB = !tracked && !callee)
            }
        run(variants)
    }

    // I. Integer controls. z = y.value without a result filter, and the sinks on y.value or on y with an ANY tail: B is
    // found at no K with an ordinary mark, and confirmed with a primitive-tracking mark. With the result filter that
    // production puts on an int read (z = y.value: int), the exact fact loses the ordinary mark at the int level too.
    // The same Integer value seen as Number or Object has no policy.

    @Test
    fun `I Integer controls - a boxed level drops an ordinary mark and keeps a primitive-tracking mark`() {
        val integer = ModelType.INTEGER
        val variants = ArrayList<Variant>()
        for (prefix in listOf(1, 2, 4)) {
            val confirm = fr(prefix + 1)
            for (tracked in marks()) {
                val base = "I prefix=$prefix"
                val b = if (tracked) confirm else null
                variants += Variant("$base D5 z = y.value (no result filter), B(z) ${tag(tracked)}", prefix, listOf(Acc.I_VALUE),
                    listOf(use(integer), read(null, Acc.I_VALUE)), emptyList(), tracked = tracked, confirm = b, losesB = !tracked)
                variants += Variant("$base z = y.value: int, B(z) ${tag(tracked)}", prefix, listOf(Acc.I_VALUE),
                    listOf(use(integer), read(ModelType.INT, Acc.I_VALUE)), emptyList(), tracked = tracked, confirm = b)
                variants += Variant("$base B(y.value) ${tag(tracked)}", prefix, listOf(Acc.I_VALUE), listOf(use(integer)),
                    listOf(Acc.I_VALUE), tracked = tracked, confirm = b, losesB = !tracked)
                variants += Variant("$base B(y has T anywhere) ${tag(tracked)}", prefix, listOf(Acc.I_VALUE), listOf(use(integer)),
                    emptyList(), sinkAny = true, tracked = tracked, confirm = b, losesB = !tracked)
            }
            variants += Variant("I prefix=$prefix Number y, B(y.value) mark=T", prefix, listOf(Acc.I_VALUE), listOf(use(ModelType.NUMBER)),
                listOf(Acc.I_VALUE), confirm = confirm)
            variants += Variant("I prefix=$prefix Object y, B(y.value) mark=T", prefix, listOf(Acc.I_VALUE), listOf(use(ModelType.OBJECT)),
                listOf(Acc.I_VALUE), confirm = confirm)
        }
        run(variants)
    }

    // P. True primitive arrays (int[], byte[], char[], int[][]): the primitive level has no fields, so no exact fact
    // lies below it. The policy drops the exact leaf at that level and the cut leaf there alike.

    @Test
    fun `P primitive arrays are unchanged`() {
        val variants = ArrayList<Variant>()
        for (element in listOf(ModelType.INT, ModelType.BYTE, ModelType.CHAR)) for (prefix in listOf(1, 3)) for (tracked in marks()) {
            val array = ModelType.array(element)
            val confirm = if (tracked) fr(prefix + 1) else null
            val base = "P ${array.name} prefix=$prefix"
            variants += Variant("$base B(y[e]) ${tag(tracked)}", prefix, listOf(Acc.E), listOf(use(array)), listOf(Acc.E),
                tracked = tracked, confirm = confirm)
            variants += Variant("$base z = y[e]: ${element.name}, B(z) ${tag(tracked)}", prefix, listOf(Acc.E), listOf(use(array), read(element, Acc.E)),
                emptyList(), tracked = tracked, confirm = confirm)
        }
        for (prefix in listOf(1, 3)) for (tracked in marks()) variants += Variant("P int[][] prefix=$prefix B(y[e][e]) ${tag(tracked)}", prefix,
            listOf(Acc.E, Acc.E), listOf(use(ModelType.array(ModelType.INT, 2))), listOf(Acc.E, Acc.E), tracked = tracked,
            confirm = if (tracked) fr(prefix + 2) else null)
        run(variants)
    }

    // U. A user class with fields: no mark policy.

    @Test
    fun `U user class holder is unchanged`() {
        val variants = ArrayList<Variant>()
        for (prefix in listOf(1, 2, 4)) {
            variants += Variant("U Box prefix=$prefix B(y.value)", prefix, listOf(Acc.BOX_VALUE), listOf(use(ModelType.BOX)),
                listOf(Acc.BOX_VALUE), confirm = fr(prefix + 1))
            variants += Variant("U Box prefix=$prefix z = y.value: Box, B(z)", prefix, listOf(Acc.BOX_VALUE),
                listOf(use(ModelType.BOX), read(ModelType.BOX, Acc.BOX_VALUE)), emptyList(), confirm = fr(prefix + 1))
        }
        run(variants)
    }
}

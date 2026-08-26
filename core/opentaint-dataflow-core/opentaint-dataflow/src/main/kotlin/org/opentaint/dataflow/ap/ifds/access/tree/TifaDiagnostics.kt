package org.opentaint.dataflow.ap.ifds.access.tree

import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger
import java.util.concurrent.atomic.AtomicLong

/**
 * Where the initial-fact abstraction's premises come from.
 *
 * Premises are emitted by WALKING `MethodSameBaseInitialFact.added` -- the merged tree of every fact
 * that has arrived at this `(method entry point, access-path base)`. So the premise count is a
 * function of how big and how branchy that tree is, and the question "why so many premises" is
 * really "why is `added` so large".
 *
 * The counters split the answer three ways: how much is ARRIVING (facts merged in, and how many of
 * those actually grew the tree), how much the tree GREW to, and how much the walk EMITS per unit of
 * tree. A method with a small `added` and many emits has a branchy walk; a method with a huge
 * `added` has an arrival problem, and the arrivals come from summary application.
 *
 * `-Dopentaint.tifaDiag=true`.
 */
object TifaDiagnostics {
    val enabled: Boolean = System.getProperty("opentaint.tifaDiag")?.trim().toBoolean()

    /** Facts handed to the abstraction, and how many of them actually grew `added`. */
    val addCalls = AtomicLong()
    val addDeltas = AtomicLong()

    /** Walk cost: states popped, premises emitted, and how many states crossed an `[any]` edge. */
    val walkStates = AtomicLong()
    val emits = AtomicLong()
    val anyDescents = AtomicLong()

    /**
     * The two ways an `[any]` can be responsible for a premise, separated.
     *
     * [emitsUnderAny] is a premise the walk produced while STANDING under an `[any]` -- the position
     * was reached by crossing one, so the `[any]` is what made the path reachable at all.
     * [emitsWithAnyInChain] is the narrower case where the `[any]` also survives INTO the emitted
     * chain. The premise census says almost no stored premise carries an `[any]`, so the gap between
     * these two columns is the whole question: it is the count of premises the `[any]` produced and
     * then vanished from.
     */
    val emitsUnderAny = AtomicLong()
    val emitsWithAnyInChain = AtomicLong()

    /**
     * The four `[any]` rules of the never-unroll walk, counted where they fire.
     *
     *  - [emitsAnyFrontier] R3a: one coarse `p.[any]` for a level that carries demand.
     *  - [emitsUncoveredFrontier] R3b: `p.[any].u` for a mark, `[value]` or type-info accessor below
     *    an `[any]`, which `p.[any]` does NOT denote. Its sibling `p.u` -- the zero-times reading --
     *    goes through the ordinary per-accessor helper and is not separable here.
     *  - [emitsSynthesised] R3c: `p.a` for an accessor demanded at this level, covered by the
     *    `[any]`, and present in no concrete branch. This is the count that replaces
     *    `unrollMaterialised`, and the comparison between them is the point of the change: the
     *    unroll's version of this emitted the same premise AND copied the carrier.
     *  - [virtualDescents] R4: a walk state entered through `getChild` rather than through an edge
     *    the fact holds. Nothing is stored, so this is pure read.
     */
    val emitsAnyFrontier = AtomicLong()
    val emitsUncoveredFrontier = AtomicLong()
    val emitsSynthesised = AtomicLong()
    val virtualDescents = AtomicLong()

    /**
     * Extra walks over the same fact, driven by "the last round registered a premise the trie did
     * not hold". Round 0 is not counted, so this is the ladder's height above the ground: 0 means
     * every base was answered in one pass.
     */
    val walkRounds = AtomicLong()

    /**
     * Arrivals at an initial-fact abstraction, split by whether the INCOMING fact carried an `[any]`,
     * and how many nodes each kind actually contributed.
     *
     * `added` is the union of arrivals, so this is where a tree that is 86-99% `[any]`-owning has to
     * come from -- either the arrivals carry it or something local manufactures it.
     */
    val arrivalsWithAny = AtomicLong()
    val arrivalNodesWithAny = AtomicLong()
    val arrivalDeltaWithAny = AtomicLong()
    val arrivalsConcrete = AtomicLong()
    val arrivalNodesConcrete = AtomicLong()
    val arrivalDeltaConcrete = AtomicLong()


    /**
     * Bases over this size get their arrivals traced and their final tree retained for an exact dump.
     * Everything below it is counted only.
     */
    const val TRACE_MIN_SIZE = 5_000L

    /** Arrivals recorded per traced base, and stack traces captured, both bounded. */
    const val TRACE_MAX_ARRIVALS = 80
    const val TRACE_MAX_STACKS = 12

    /**
     * The TARGETED trace: a substring of the `"<base> @ <method>"` key. Every base whose key
     * contains it records EVERY arrival from the very first one, each attributed to the call site
     * that produced it.
     *
     * [TRACE_MIN_SIZE] exists so that a whole-project run does not retain thousands of trees, but
     * it means the recorded ladder starts at 5,000 nodes -- it can only ever show the TAIL of an
     * explosion. Answering "where did this tree come from" needs the ladder to start at the seed,
     * which is what this does, for one base chosen up front.
     *
     * `-Dopentaint.tifaTrace=<substring of the key>`.
     */
    val traceKey: String? = System.getProperty("opentaint.tifaTrace")?.trim()?.takeIf { it.isNotEmpty() }

    /** Arrivals kept for a targeted base. Deliberately large: the ladder IS the result. */
    const val TRACE_TARGET_MAX = 6_000

    /** Matching bases dumped in full; the rest are listed as one summary line each. */
    const val TRACE_TARGET_DUMPS = 2

    /**
     * Render field edges as `className#fieldName:fieldType` instead of `.fieldName`.
     *
     * `FieldAccessor.toSuffix()` is `".$fieldName"` and drops the declaring class, so the dump
     * cannot distinguish two different classes' identically-named fields -- and, more importantly,
     * cannot show whether a chain is type-feasible. `-Dopentaint.tifaLongLabels=true`.
     */
    val longLabels: Boolean = System.getProperty("opentaint.tifaLongLabels")?.trim().toBoolean()

    /** How many bases the end-of-run report lists. `-Dopentaint.tifaTop=N`. */
    val reportTopN: Int = System.getProperty("opentaint.tifaTop")?.trim()?.toIntOrNull() ?: 20

    /**
     * The call statement currently being propagated by [org.opentaint.dataflow.ap.ifds.MethodAnalyzer].
     *
     * An arrival at a callee's `added` is caused by a caller subscribing at a call site, and that
     * call site is the only object in the whole chain that names a line of the ANALYSED PROGRAM.
     * It is not reachable from the abstraction, so the call step parks it here and the arrival
     * reads it back. The statement object is parked, not a string: [callStatementStep] runs
     * millions of times and an arrival is recorded thousands of times, so the formatting has to
     * happen on the rare side.
     *
     * Written only when [parkingEnabled], and restored by the same `finally` that set it. Restored
     * rather than cleared: a summary application parks its own call statement INSIDE a call step
     * that has already parked one, and clearing would leave the outer step attributing its
     * remaining work to nothing.
     */
    val callSite: ThreadLocal<Any?> = ThreadLocal()

    /**
     * Whether the call statement is parked at all.
     *
     * [ApOpDiagnostics] bills the summary graft to a line of the analysed program and reads the same
     * thread local, and [SummaryPremiseDiagnostics] bills a premise the same way, so parking cannot
     * be conditioned on `tifaDiag` alone.
     */
    val parkingEnabled: Boolean = enabled || ApOpDiagnostics.enabled || SummaryPremiseDiagnostics.enabled

    /** Park [statement] for the duration of [body], restoring whatever was parked before. */
    inline fun <T> withCallSite(statement: Any?, body: () -> T): T {
        if (!parkingEnabled) return body()
        val previous = callSite.get()
        callSite.set(statement)
        try {
            return body()
        } finally {
            callSite.set(previous)
        }
    }

    private val locationAccessors = ConcurrentHashMap<Class<*>, Array<java.lang.reflect.Method?>>()

    /**
     * `<declaring method>:<line>` for an instruction, best effort.
     *
     * Reflective because `CommonInstLocation` carries only `method` and `index` -- the line number
     * exists on the JVM implementation and this module cannot see that type. A wrong guess here
     * costs a "?" in a diagnostic, so the failure mode is acceptable; being unable to name a line
     * of the analysed program is not.
     */
    fun siteOf(statement: Any?): String {
        if (statement == null) return "no-call-site"
        return runCatching {
            val acc = locationAccessors.computeIfAbsent(statement.javaClass) { cls ->
                val getLocation = runCatching { cls.getMethod("getLocation") }.getOrNull()
                    ?.also { it.isAccessible = true }
                val loc = getLocation?.invoke(statement)
                val getMethod = loc?.let { runCatching { it.javaClass.getMethod("getMethod") }.getOrNull() }
                    ?.also { it.isAccessible = true }
                val getLine = loc?.let { runCatching { it.javaClass.getMethod("getLineNumber") }.getOrNull() }
                    ?.also { it.isAccessible = true }
                arrayOf(getLocation, getMethod, getLine)
            }
            val loc = acc[0]?.invoke(statement) ?: return "?"
            val method = acc[1]?.invoke(loc)?.toString() ?: "?"
            val line = acc[2]?.invoke(loc)?.toString() ?: "?"
            "$method:$line"
        }.getOrElse { "?" }
    }

    private val perBase = ConcurrentHashMap<String, BaseStats>()

    fun baseStats(key: String): BaseStats = perBase.computeIfAbsent(key) { BaseStats(it) }

    /**
     * The full ladder for every base matching [traceKey], largest first.
     *
     * The top [TRACE_TARGET_DUMPS] get the whole DAG plus every arrival; the rest get one line, so
     * that a loose key degrades into a census rather than into gigabytes of output.
     */
    fun dumpTargeted(): String {
        val key = traceKey ?: return "no trace key set"
        val hits = perBase.entries.filter { it.key.contains(key) }
            .sortedByDescending { it.value.maxAddedSize.get() }
        if (hits.isEmpty()) return "no (base, method) pair matched trace key '$key'"
        return buildString {
            appendLine("TARGETED TRACE for '$key' -- ${hits.size} matching (base, method) pairs")
            hits.take(TRACE_TARGET_DUMPS).forEach { appendLine(it.value.dumpTree()) }
            if (hits.size > TRACE_TARGET_DUMPS) {
                appendLine("  --- ${hits.size - TRACE_TARGET_DUMPS} further matches, summary only ---")
                hits.drop(TRACE_TARGET_DUMPS).forEach { appendLine("    ${it.value}") }
            }
        }
    }

    /** The exact shape and content of the single largest `added`, plus how it got there. */
    fun dumpLargest(): String {
        val worst = perBase.values.maxByOrNull { it.maxAddedSize.get() } ?: return "no bases"
        return worst.dumpTree()
    }

    fun report(topN: Int): String {
        val all = perBase.values.sortedByDescending { it.maxAddedSize.get() }
        return buildString {
            append("tifa addCalls=").append(addCalls.get())
            append(" addDeltas=").append(addDeltas.get())
            append(" walkStates=").append(walkStates.get())
            append(" emits=").append(emits.get())
            append(" anyDescents=").append(anyDescents.get())
            append(" walkRounds=").append(walkRounds.get())
            append(" R3a=").append(emitsAnyFrontier.get())
            append(" R3b=").append(emitsUncoveredFrontier.get())
            append(" R3c=").append(emitsSynthesised.get())
            append(" R4=").append(virtualDescents.get())
            appendLine()
            append("tifa emitsUnderAny=").append(emitsUnderAny.get())
            append(" emitsWithAnyInChain=").append(emitsWithAnyInChain.get())
            append(" | arrivals any/concrete=").append(arrivalsWithAny.get()).append("/").append(arrivalsConcrete.get())
            append(" incomingNodes any/concrete=").append(arrivalNodesWithAny.get()).append("/").append(arrivalNodesConcrete.get())
            append(" addedDelta any/concrete=").append(arrivalDeltaWithAny.get()).append("/").append(arrivalDeltaConcrete.get())
            appendLine()
            appendLine("added trees: ${all.size} (method, base) pairs")
            all.take(topN).forEach { appendLine("  $it") }
        }
    }
}

class BaseStats(private val key: String) {
    /** Whether this base is the one [TifaDiagnostics.traceKey] asked for the full ladder of. */
    private val targeted: Boolean = TifaDiagnostics.traceKey?.let { key.contains(it) } == true

    /** Nodes in `added`, counted with multiplicity -- the precomputed subtree size. */
    @JvmField val maxAddedSize = AtomicLong()

    /** Its depth, which separates "wide" from "deep". */
    @JvmField val maxAddedDepth = AtomicInteger()

    /** Whether this base's `added` ever carried an `[any]` anywhere. */
    @JvmField val everCarriedAny = AtomicInteger()

    @JvmField val addCalls = AtomicLong()
    @JvmField val emits = AtomicLong()

    /** The same `[any]` split as [TifaDiagnostics], per base -- see the doc there. */
    @JvmField val emitsUnderAny = AtomicLong()
    @JvmField val emitsWithAnyInChain = AtomicLong()
    @JvmField val arrivalsWithAny = AtomicLong()
    @JvmField val arrivalDeltaWithAny = AtomicLong()
    @JvmField val arrivalsConcrete = AtomicLong()
    @JvmField val arrivalDeltaConcrete = AtomicLong()

    /**
     * A structural profile of the largest `added` seen, recomputed only when the tree DOUBLES past
     * a threshold -- a handful of times per big base, never for a small one.
     */
    @Volatile
    @JvmField
    var profile: String? = null

    @Volatile
    private var profiledAt: Long = 0

    /** The final tree, retained only for bases big enough to be worth an exact dump. */
    @Volatile
    private var retained: AccessTree.AccessNode? = null

    /**
     * The SEED: the very first fact that ever arrived at this base, recorded for every base.
     *
     * One string per base, so it is affordable everywhere, and it is the only way to see where a
     * tree STARTED -- every other record here is thresholded and therefore shows only the tail.
     */
    @Volatile
    @JvmField
    var firstArrival: String? = null

    /** What arrived, in order: `size-before -> size-after  <the incoming fact>`. */
    private val arrivals = java.util.Collections.synchronizedList(ArrayList<String>())
    private val stacks = java.util.Collections.synchronizedList(ArrayList<String>())

    fun recordArrival(before: AccessTree.AccessNode?, incoming: AccessTree.AccessNode, after: AccessTree.AccessNode) {
        val delta = after.size - (before?.size ?: 0)
        if (incoming.containsAnyInThisOrDeepNodes) {
            arrivalsWithAny.incrementAndGet()
            arrivalDeltaWithAny.addAndGet(delta)
            TifaDiagnostics.arrivalsWithAny.incrementAndGet()
            TifaDiagnostics.arrivalNodesWithAny.addAndGet(incoming.size)
            TifaDiagnostics.arrivalDeltaWithAny.addAndGet(delta)
        } else {
            arrivalsConcrete.incrementAndGet()
            arrivalDeltaConcrete.addAndGet(delta)
            TifaDiagnostics.arrivalsConcrete.incrementAndGet()
            TifaDiagnostics.arrivalNodesConcrete.addAndGet(incoming.size)
            TifaDiagnostics.arrivalDeltaConcrete.addAndGet(delta)
        }

        if (firstArrival == null) {
            firstArrival = "at ${TifaDiagnostics.siteOf(TifaDiagnostics.callSite.get())}: " +
                incoming.toString().replace('\n', ' ').take(300)
        }

        if (targeted) {
            recordTargetedArrival(before, incoming, after)
            return
        }

        if (after.size < TifaDiagnostics.TRACE_MIN_SIZE) return

        if (arrivals.size < TifaDiagnostics.TRACE_MAX_ARRIVALS) {
            arrivals.add(
                "${before?.size ?: 0} -> ${after.size} (+${after.size - (before?.size ?: 0)})" +
                    " incoming size=${incoming.size} depth=${incoming.maxDepth}: " +
                    incoming.toString().replace('\n', ' ').take(400)
            )
        }

        if (stacks.size < TifaDiagnostics.TRACE_MAX_STACKS) {
            val frames = Thread.currentThread().stackTrace
                .map { it.toString() }
                .filter { it.startsWith("org.opentaint") }
                .filterNot { it.contains("TifaDiagnostics") }
                .take(22)
                .joinToString("\n        ")
            stacks.add("at added.size=${after.size}\n        $frames")
        }
    }

    /**
     * Every arrival, numbered, with the call site that caused it and the distinct-node count.
     *
     * `distinct` rather than `size` is what makes this readable: `size` counts with multiplicity,
     * so a tree can triple in `size` without a single new node being allocated. A step where
     * `distinct` moves is a step where the fact learned a new SHAPE; a step where only `size`
     * moves is the same shape reached along more paths.
     */
    private fun recordTargetedArrival(
        before: AccessTree.AccessNode?,
        incoming: AccessTree.AccessNode,
        after: AccessTree.AccessNode,
    ) {
        if (arrivals.size >= TifaDiagnostics.TRACE_TARGET_MAX) return
        val beforeSize = before?.size ?: 0
        val beforeDistinct = before?.countNodes() ?: 0
        val afterDistinct = after.countNodes()
        arrivals.add(
            "#${arrivals.size} size ${beforeSize}->${after.size} (+${after.size - beforeSize})" +
                " distinct ${beforeDistinct}->${afterDistinct} (+${afterDistinct - beforeDistinct})" +
                " depth=${after.maxDepth}" +
                " | at ${TifaDiagnostics.siteOf(TifaDiagnostics.callSite.get())}" +
                " | incoming size=${incoming.size} distinct=${incoming.countNodes()}" +
                " depth=${incoming.maxDepth}: " +
                incoming.toString().replace('\n', ' ').take(320)
        )
    }

    fun dumpTree(): String {
        val root = retained ?: return "no retained tree for $key"
        return buildString {
            appendLine("EXACT TREE for $key")
            appendLine("  size(multiplicity)=${root.size} distinct=${root.countNodes()} depth=${root.maxDepth}")
            appendLine("  --- DAG (shared nodes appear once; `=> nK` is a back-reference) ---")
            val ids = java.util.IdentityHashMap<AccessTree.AccessNode, Int>()
            val order = ArrayList<AccessTree.AccessNode>()
            fun assign(n: AccessTree.AccessNode) {
                if (ids.containsKey(n)) return
                ids[n] = ids.size
                order.add(n)
                n.forEachAccessor { _, c -> assign(c) }
            }
            assign(root)
            for (n in order) {
                val flags = buildString {
                    if (n.isAbstract) append("*")
                    if (n.isFinal) append("$")
                    if (n.deepAccessorExclusion != null) append("[excl]")
                }

                // The `[any]` manager position this node sits at, and its kind.
                //
                // Without it the dump can say a node owns an `[any]` but not why nothing absorbed
                // into it, which is the question every large fact raises. `PAID` here means every
                // prepend above this node wrote its step; `CREDIT` means the node was eligible and
                // something else declined.
                val any = n.anyId?.let { state ->
                    val manager = n.manager.anyUnroll
                    val dag = manager.dagOf(state)
                    " [any]@s${state.find().id}/${manager.kindOf(state)}" +
                        (dag?.let { " dag#${it.id}(total=${it.total},states=${it.states})" } ?: "")
                }.orEmpty()

                appendLine("  n${ids[n]}$flags$any")
                n.forEachAccessor { accessor, child ->
                    val a = with(n.manager) { accessor.accessor }
                    val name = if (TifaDiagnostics.longLabels && a is org.opentaint.dataflow.ap.ifds.FieldAccessor) {
                        ".${a.fieldName} {${a.className} : ${a.fieldType}}"
                    } else {
                        a.toSuffix()
                    }
                    appendLine("      $name => n${ids[child]}")
                }
            }
            appendLine("  --- the seed: ${firstArrival ?: "never recorded"} ---")
            val how = if (targeted) {
                "  --- how it grew: all ${arrivals.size} arrivals, from the seed ---"
            } else {
                "  --- how it grew: the first ${arrivals.size} arrivals that reached the threshold ---"
            }
            appendLine(how)
            arrivals.forEach { appendLine("    $it") }
            appendLine("  --- who added them ---")
            stacks.forEach { appendLine("    $it") }
        }
    }

    fun recordAdded(node: AccessTree.AccessNode) {
        var cur = maxAddedSize.get()
        while (node.size > cur && !maxAddedSize.compareAndSet(cur, node.size)) cur = maxAddedSize.get()

        var d = maxAddedDepth.get()
        while (node.maxDepth > d && !maxAddedDepth.compareAndSet(d, node.maxDepth)) d = maxAddedDepth.get()

        if (node.containsAnyInThisOrDeepNodes) everCarriedAny.set(1)

        if (node.size >= PROFILE_MIN_SIZE && node.size >= profiledAt * 2) {
            profiledAt = node.size
            profile = profileOf(node)
        }

        // Always the LATEST tree over the threshold, not a doubling snapshot: the previous instrument
        // caught this base at 20,601 and reported `anyEdges=0`, while its recorded max depth of 127
        // implies about eleven `[any]` edges stacked on one path in the version that actually mattered.
        if (targeted || node.size >= TifaDiagnostics.TRACE_MIN_SIZE) retained = node
    }

    private fun profileOf(root: AccessTree.AccessNode): String {
        // Distinct nodes vs `size`: `size` counts with multiplicity, so the ratio is how much
        // sharing the interner has already bought. A tree that is 32k by multiplicity and 300
        // distinct is a very different object from one that is 32k of both.
        val distinct = root.countNodes()

        val perLevel = HashMap<Int, MutableSet<AccessTree.AccessNode>>()
        val accessorCounts = HashMap<String, Int>()
        var anyEdges = 0
        val anyDepths = sortedSetOf<Int>()
        var deepest = ""

        val seen = java.util.IdentityHashMap<AccessTree.AccessNode, Int>()
        val stack = ArrayDeque<Triple<AccessTree.AccessNode, Int, String>>()
        stack.addLast(Triple(root, 0, ""))
        var visits = 0

        while (stack.isNotEmpty() && visits < PROFILE_VISIT_BUDGET) {
            val (node, depth, path) = stack.removeLast()
            visits++

            perLevel.getOrPut(depth) { java.util.Collections.newSetFromMap(java.util.IdentityHashMap()) }.add(node)
            if (path.length > deepest.length) deepest = path
            if (seen.put(node, depth) != null) continue

            node.forEachAccessor { accessor, child ->
                val name = with(node.manager) { accessor.accessor }.toSuffix()
                accessorCounts.merge(name, 1, Int::plus)
                if (accessor == ANY_ACCESSOR_IDX) {
                    anyEdges++
                    anyDepths.add(depth)
                }
                stack.addLast(Triple(child, depth + 1, path + name))
            }
        }

        val levels = (0..perLevel.keys.maxOrNull().orZeroInt())
            .joinToString(",") { perLevel[it]?.size?.toString() ?: "0" }
        val topAccessors = accessorCounts.entries.sortedByDescending { it.value }.take(8)
            .joinToString(", ") { "${it.key}:${it.value}" }

        return buildString {
            append("size=").append(root.size)
            append(" distinct=").append(distinct)
            append(" depth=").append(root.maxDepth)
            append(" anyEdges=").append(anyEdges)
            append(" anyDepths=").append(anyDepths.take(12))
            append(if (visits >= PROFILE_VISIT_BUDGET) " TRUNCATED" else "")
            append(" | levels=").append(levels.take(200))
            append(" | top=").append(topAccessors)
            append(" | deepest=").append(deepest.take(300))
        }
    }

    private fun Int?.orZeroInt(): Int = this ?: 0

    private companion object {
        const val PROFILE_MIN_SIZE = 5_000L
        const val PROFILE_VISIT_BUDGET = 400_000
    }

    override fun toString(): String = buildString {
        append("added: ").append(maxAddedSize.get())
        append(" | depth: ").append(maxAddedDepth.get())
        append(" | any: ").append(everCarriedAny.get())
        append(" | adds: ").append(addCalls.get())
        append(" | emits: ").append(emits.get())
        append(" | underAny: ").append(emitsUnderAny.get())
        append(" | inChain: ").append(emitsWithAnyInChain.get())
        append(" | arr any/con: ").append(arrivalsWithAny.get()).append("/").append(arrivalsConcrete.get())
        append(" | dNodes any/con: ").append(arrivalDeltaWithAny.get()).append("/").append(arrivalDeltaConcrete.get())
        append(" | ").append(key)
        firstArrival?.let { append("\n      SEED ").append(it) }
        profile?.let { append("\n      PROFILE ").append(it) }
    }
}

package org.opentaint.dataflow.ap.ifds.access.tree

import it.unimi.dsi.fastutil.ints.Int2ObjectOpenHashMap
import it.unimi.dsi.fastutil.ints.IntArrayList
import it.unimi.dsi.fastutil.ints.IntList
import it.unimi.dsi.fastutil.ints.IntObjectImmutablePair
import it.unimi.dsi.fastutil.ints.IntOpenHashSet
import it.unimi.dsi.fastutil.objects.Object2ObjectOpenHashMap
import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.FinalAccessor
import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion
import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion.Companion.addAccessorFromDepth0
import org.opentaint.dataflow.ap.ifds.access.DeepAccessorExclusion.Companion.addAccessorFromDepth1
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.ReversedApNode
import org.opentaint.dataflow.ap.ifds.access.tree.AccessPath.AccessNode.Companion.foldRight
import org.opentaint.dataflow.ap.ifds.access.util.AccessorIdx
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ANY_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.ELEMENT_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.FINAL_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.TYPE_INFO_GROUP_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.VALUE_ACCESSOR_IDX
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isFieldAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isStaticAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.util.AccessorInterner.Companion.isTypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.serialization.DeepExclusionsSerializer
import org.opentaint.dataflow.ap.ifds.serialization.SummarySerializationContext
import org.opentaint.dataflow.util.Cancellation
import org.opentaint.dataflow.util.forEachInt
import org.opentaint.dataflow.util.forEachIntEntry
import org.opentaint.dataflow.util.getOrCreate
import org.opentaint.dataflow.util.reversedForEachInt
import java.io.DataInputStream
import java.io.DataOutputStream
import java.util.IdentityHashMap
import java.util.Optional
import kotlin.jvm.optionals.getOrNull

class AccessTree(
    val apManager: TreeApManager,
    override val base: AccessPathBase,
    val access: AccessNode,
    override val exclusions: ExclusionSet,
    /**
     * The manager state of an `[any]` edge just taken OFF this fact, so that prepending one back
     * reuses it instead of minting a fresh origin.
     *
     * Deliberately on the WRAPPER and not on [AccessNode]. Three things follow from that and each
     * one matters: it costs the node nothing and adds no second axis to the interner; storages hold
     * bare nodes, so it cannot leak into persistent state, which is right because dormancy is a
     * within-operation notion; and, most sharply, it cannot break the one reference comparison the
     * whole loop fixpoint rests on. A dormant id in node identity would make `abstractNode` and
     * `abstractNode(dormant = X)` distinct objects, `mergeAddStep` would rebuild instead of
     * returning the receiver, and every loop in the program would cost extra laps.
     *
     * It is NOT part of equality or the hash, for the same reason.
     */
    private val dormantAnyId: AnyUnrollState? = null,
) : FinalFactAp {
    override fun rebase(newBase: AccessPathBase): FinalFactAp =
        AccessTree(apManager, newBase, access, exclusions, dormantAnyId)

    override fun exclude(accessor: Accessor): FinalFactAp =
        AccessTree(apManager, base, access, exclusions.add(accessor), dormantAnyId)

    override fun replaceExclusions(exclusions: ExclusionSet): FinalFactAp =
        AccessTree(apManager, base, access, exclusions, dormantAnyId)

    override fun getAllAccessors(): Set<Accessor> {
        val result = IntOpenHashSet()
        access.collectAccessorsTo(result)

        return result.mapTo(hashSetOf()) {
            with(apManager) { it.accessor }
        }
    }

    override fun startsWithAccessor(accessor: Accessor): Boolean =
        with(apManager) { access.contains(accessor.idx) }

    override fun getStartAccessors(): Set<Accessor> = with(apManager) {
        access.accessors?.mapTo(hashSetOf()) { it.accessor }.orEmpty()
    }

    override fun isAbstract(): Boolean = access.isAbstract

    override fun readAccessor(accessor: Accessor): FinalFactAp? = with(apManager) {
        val idx = accessor.idx
        access.getChildRecording(idx)
            ?.let { AccessTree(apManager, base, it, exclusions, dormantAnyIdAfterRemoving(idx)) }
    }

    override fun prependAccessor(accessor: Accessor): FinalFactAp = with(apManager) {
        AccessTree(apManager, base, access.addParent(accessor.idx, dormantAnyId), exclusions)
    }

    override fun clearAccessor(accessor: Accessor): FinalFactAp? = with(apManager) {
        val idx = accessor.idx
        val newAccess = access.clearChild(idx).takeIf { !it.isEmpty } ?: return null
        return AccessTree(apManager, base, newAccess, exclusions, dormantAnyIdAfterRemoving(idx))
    }

    /**
     * Reading or clearing the `[any]` accessor and then prepending one back is a round trip that
     * should be free; without this it burns a fresh origin every lap. One file in the engine does it
     * across operations -- the cleaner -- which is exactly the case the wrapper can carry.
     */
    private fun dormantAnyIdAfterRemoving(accessorIdx: AccessorIdx): AnyUnrollState? =
        if (accessorIdx == ANY_ACCESSOR_IDX) access.anyId else dormantAnyId

    override fun removeAbstraction(): FinalFactAp? =
        access.removeAbstraction().takeIf { !it.isEmpty }
            ?.let { AccessTree(apManager, base, it, exclusions, dormantAnyId) }

    override fun abstractOnly(): FinalFactAp =
        // `abstractOnly` DROPS every child edge including the `[any]`, so its state has nowhere left
        // to live on the node -- which is precisely when the wrapper should keep it.
        AccessTree(apManager, base, access.abstractOnly(), exclusions, access.anyId ?: dormantAnyId)

    override fun clearAllAccessorOccurrences(
        accessor: Accessor,
        keepStartAccessor: Boolean,
    ): FinalFactAp? {
        val accessorIdx = with(apManager) { accessor.idx }
        val cleared = access.clearAllAccessorOccurrences(
            accessorIdx, keepStartAccessor, retainDeepAccessorExclusions = exclusions !is ExclusionSet.Universe, IdentityHashMap()
        ) ?: return null

        return if (cleared === access) this else AccessTree(apManager, base, cleared, exclusions, dormantAnyId)
    }

    override fun filterFact(filter: FactTypeChecker.FactApFilter): FinalFactAp? {
        val filteredAccess = access.filterAccessNode(filter) ?: return null
        return AccessTree(apManager, base, filteredAccess, exclusions, dormantAnyId)
    }

    override fun filterFact(filter: FactTypeChecker.FactCompatibilityFilter): FinalFactAp? {
        if (filter is FactTypeChecker.AlwaysCompatibleFilter) return this
        val filteredAccess = access.filterAccessNode(filter) ?: return null
        return AccessTree(apManager, base, filteredAccess, exclusions, dormantAnyId)
    }

    override fun contains(factAp: InitialFactAp): Boolean {
        factAp as AccessPath

        if (base != factAp.base) return false

        return access.contains(factAp.access)
    }

    override fun equalTo(factAp: InitialFactAp): Boolean {
        factAp as AccessPath

        if (base != factAp.base) return false

        return access.equalTo(factAp.access)
    }

    private sealed interface AccessTreeDelta : FinalFactAp.Delta

    data class EmptyAccessTreeDelta(
        val deepAccessorExclusion: DeepAccessorExclusion?,
    ) : AccessTreeDelta {
        override val isEmpty: Boolean get() = true
        override fun startsWithAccessor(accessor: Accessor): Boolean = false
        override fun getStartAccessors(): Set<Accessor> = emptySet()
        override fun getAllAccessors(): Set<Accessor> = emptySet()
        override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = null
        override fun isAbstract(): Boolean = true
    }

    data class NodeAccessTreeDelta(
        private val apManager: TreeApManager,
        val node: AccessNode
    ) : AccessTreeDelta {
        override val isEmpty: Boolean get() = false

        override fun startsWithAccessor(accessor: Accessor): Boolean = with(apManager) {
            node.contains(accessor.idx)
        }

        override fun getStartAccessors(): Set<Accessor> = with(apManager) {
            node.accessors?.mapTo(hashSetOf()) { it.accessor }.orEmpty()
        }

        override fun getAllAccessors(): Set<Accessor> = with(apManager) {
            val s = IntOpenHashSet()
            node.collectAccessorsTo(s)
            return s.mapTo(hashSetOf()) { it.accessor }
        }

        override fun readAccessor(accessor: Accessor): FinalFactAp.Delta? = with(apManager) {
            node.getChildRecording(accessor.idx)
                ?.let { NodeAccessTreeDelta(apManager, it) }
        }

        override fun isAbstract(): Boolean = node.isAbstract
    }

    override fun delta(other: InitialFactAp): List<FinalFactAp.Delta> {
        other as AccessPath

        if (base != other.base) return emptyList()

        val crossed = if (ApOpDiagnostics.enabled) {
            ApOpDiagnostics.crossedAnyFlag.get().also { it.value = 0 }
        } else null

        val deltaResult = deltaImpl(other)

        if (ApOpDiagnostics.enabled) {
            var links = 0
            var carriesAny = false
            other.access?.toList()?.forEachInt { a ->
                links++
                if (a == ANY_ACCESSOR_IDX) carriesAny = true
            }
            val remainderNodes = deltaResult.sumOf { (it as? NodeAccessTreeDelta)?.node?.size ?: 0L }
            ApOpDiagnostics.recordDelta(
                premiseCarriesAny = carriesAny,
                factNodes = access.size,
                premiseLinks = links,
                resultNodes = remainderNodes,
            )

            if ((crossed?.value ?: 0) > 0) {
                val keepsAny = deltaResult.any {
                    (it as? NodeAccessTreeDelta)?.node?.containsAnyInThisOrDeepNodes == true
                }
                ApOpDiagnostics.deltaThroughAny.incrementAndGet()
                ApOpDiagnostics.deltaThroughAnyFactNodes.addAndGet(access.size)
                ApOpDiagnostics.deltaThroughAnyRemainderNodes.addAndGet(remainderNodes)
                if (keepsAny) ApOpDiagnostics.deltaThroughAnyKept.incrementAndGet()
                if (remainderNodes >= access.size) ApOpDiagnostics.deltaThroughAnyNotSmaller.incrementAndGet()

                if (keepsAny && !carriesAny) {
                    // The exact hypothesis: a CONCRETE premise read through an `[any]` and the
                    // `[any]` survived into the remainder. Record it verbatim, once, so the shape
                    // can be read rather than inferred from counters.
                    ApOpDiagnostics.sampleRoundTrip {
                        "premise=" + other.toString().replace('\n', ' ').take(120) +
                            " | fact=" + this.toString().replace('\n', ' ').take(160) +
                            " | remainder=" + deltaResult.joinToString(" ; ") { d ->
                                (d as? NodeAccessTreeDelta)?.node?.toString()?.replace('\n', ' ')?.take(160)
                                    ?: "<empty>"
                            }
                    }
                }
            }
        }

        return deltaResult
    }

    private fun deltaImpl(other: AccessPath): List<FinalFactAp.Delta> {
        var node = access
        val access = other.access
        access?.toList()?.forEachInt { accessor ->
            if (accessor == FINAL_ACCESSOR_IDX) {
                if (!node.isFinal) return emptyList()
                return listOf(EmptyAccessTreeDelta(deepAccessorExclusion = null))
            }

            node = node.getChildRecording(accessor) ?: return emptyList()
        }

        val filteredNode = when (val exclusion = other.exclusions) {
            ExclusionSet.Empty -> node
            is ExclusionSet.Concrete -> node.filter(exclusion)
            ExclusionSet.Universe -> error("Unexpected universe exclusion in initial fact")
        }

        if (filteredNode.isEmpty) return emptyList()

        if (!filteredNode.isAbstract) return listOf(NodeAccessTreeDelta(apManager, filteredNode))

        val nonAbstractDelta = filteredNode
            .removeAbstraction()
            .takeIf { !it.isEmpty }
            ?.let { NodeAccessTreeDelta(apManager, it) }

        return listOfNotNull(nonAbstractDelta, EmptyAccessTreeDelta(filteredNode.deepAccessorExclusion))
    }

    override fun concat(typeChecker: FactTypeChecker, delta: FinalFactAp.Delta): FinalFactAp? {
        when (val d = delta as AccessTreeDelta) {
            is EmptyAccessTreeDelta -> {
                val deepAccessorExclusion = d.deepAccessorExclusion ?: return this
                val annotated = access.annotateAbstractNodes(deepAccessorExclusion, IdentityHashMap())
                if (annotated === access) return this
                return AccessTree(apManager, base, annotated, exclusions)
            }
            is NodeAccessTreeDelta -> {
                val concatenatedAccess = access.concatToLeafAbstractNodes(typeChecker, d.node)
                    ?: return null
                if (ApOpDiagnostics.enabled) {
                    ApOpDiagnostics.recordConcatBase(
                        baseKind = if (base is AccessPathBase.ClassStatic) "<static>" else base.javaClass.simpleName,
                        receiver = access.size,
                        result = concatenatedAccess.size,
                        receiverCarriesAny = access.containsAnyInThisOrDeepNodes,
                    )
                }
                return AccessTree(apManager, base, concatenatedAccess, exclusions)
            }
        }
    }

    override val size: Int
        get() = access.countNodes()

    override val depth: Int
        get() = access.maxDepth

    override fun toString(): String = buildString {
        access.print(this, "$base", suffix = "/$exclusions")
        if (this[lastIndex] == '\n') {
            this.deleteCharAt(lastIndex)
        }
    }

    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (javaClass != other?.javaClass) return false

        other as AccessTree

        if (base != other.base) return false
        if (access != other.access) return false
        if (exclusions != other.exclusions) return false

        return true
    }

    override fun hashCode(): Int {
        var result = base.hashCode()
        result = 31 * result + access.hashCode()
        result = 31 * result + exclusions.hashCode()
        return result
    }

    /**
     * A node of the access tree.
     *
     * Its booleans are NOT separate fields: all five live packed in [flags].
     *
     * [AccessNode] is the most numerous object in the analysis by a wide margin -- the prototype
     * measured facts averaging 43 nodes each across 2.6 M abstraction calls, with 22,867 individual
     * facts exceeding 1000 nodes -- and heap is the binding constraint (the target workload OOMs at
     * 8 GB). Five `Boolean` fields occupy five bytes plus alignment padding in the JVM object
     * layout; one `Byte` plus fold-away accessors removes several bytes per node.
     *
     * The constructor still takes the three CONSTRUCTED bits as named booleans rather than a packed
     * argument: there are many call sites, they all pass them by name, and a packed `Int` argument
     * would turn a transposition into a silent, near-undiscoverable bug. Packing happens once,
     * internally, next to where the two DERIVED bits are computed.
     */
    class AccessNode private constructor(
        val manager: TreeApManager,
        interned: Boolean,
        isAbstract: Boolean,
        isFinal: Boolean,
        @JvmField val deepAccessorExclusion: DeepAccessorExclusion?,
        @JvmField val accessors: IntArray?,
        @JvmField val accessorNodes: Array<AccessNode>?,
        anyIdRaw: AnyUnrollState?,
    ) {
        /**
         * The `[any]` unroll manager state owned by THIS node's `[any]` edge, or null when the node
         * owns no such edge (and always null when the feature is off).
         *
         * Canonicalised at construction -- `find()` here and the STORED REFERENCE at compare time.
         * A [hashCode] that called `find` would change over time: a union moves the representative,
         * the node's hash changes, and every hash structure already holding it silently loses the
         * entry. Canonicalising at build time instead lets the structural duplicates a union leaves
         * behind die out as the analysis rebuilds trees, which it does constantly.
         */
        @JvmField val anyId: AnyUnrollState? = anyIdRaw?.find()

        @JvmField val hash: Long
        @JvmField val size: Long
        @JvmField val maxDepth: Int

        /**
         * All five boolean properties of this node, packed.
         *
         * Assigned exactly once, from an init block, so it is a final field: safely published to
         * every thread that sees the node, which matters because nodes are shared and interned.
         *
         * WARNING: this byte mixes IDENTITY bits ([isAbstract], [isFinal]) with bits that are either
         * derived from the subtree ([containsStatic], [containsAnyInThisOrDeepNodes]) or describe the
         * node's storage state ([interned]). Comparing whole bytes in [equals] / [hashCode] /
         * [AccessTreeInterner] would therefore be WRONG -- see the comment in [equals].
         */
        @JvmField val flags: Byte

        /** Whether this node has been canonicalised by an [AccessTreeInterner]. */
        val interned: Boolean get() = (flags.toInt() and INTERNED) != 0

        val isAbstract: Boolean get() = (flags.toInt() and ABSTRACT) != 0

        val isFinal: Boolean get() = (flags.toInt() and FINAL) != 0

        val containsStatic: Boolean get() = (flags.toInt() and CONTAINS_STATIC) != 0

        /**
         * True if an `[any]` accessor is reachable from here: either on THIS node or anywhere
         * strictly below it. Derived at construction, like [containsStatic].
         *
         * The shallow counterpart is [containsAnyAccessor], which tests THIS NODE ONLY. The two
         * are easy to confuse, hence the deliberately long name -- do not shorten it.
         *
         * It exists so that the two soundness-critical [maxDepth] prefilters in [filterStartsWith]
         * can be disabled exactly where [maxDepth] under-approximates the reachable depth, i.e.
         * where [getChild] can synthesise arbitrarily deep children through an `[any]` edge.
         */
        val containsAnyInThisOrDeepNodes: Boolean get() = (flags.toInt() and CONTAINS_ANY_DEEP) != 0

        /**
         * Memoised [AccessTreeAnySuffixMatcher] for this node used as an `[any]` suffix.
         *
         * The matcher is immutable and a PURE FUNCTION of the node it is built from, so a benign
         * race that builds it twice is harmless: both copies denote the same suffix language, and
         * whichever wins the write is equally valid. That is why the field needs no lock, only
         * `@Volatile` for safe publication of the fully-built object.
         *
         * Without it the matcher is rebuilt from scratch on every merge, which is the single
         * hottest thing in the analysis once `[any]` stays symbolic in facts: measured at
         * 91,002,062 constructions costing 143 s on conductor, cut to 30.6 M / 35 s by this memo.
         *
         * It is a derived cache, NOT part of the node's identity -- [equals], [hashCode] and
         * [AccessTreeInterner.InternStrategy] must never look at it, and [markInterned] deliberately
         * does not copy it (the rebuilt node simply refills it lazily).
         */
        @Volatile
        @JvmField
        var anySuffixMatcher: AccessTreeAnySuffixMatcher? = null

        init {
            check(deepAccessorExclusion == null || isAbstract) {
                "AnyFieldAccessorExclusions on a non-abstract node"
            }
        }

        init {
            // The node-level invariant that turns the whole propagation problem into a rule a
            // reviewer can check locally at each construction site: a state is present exactly when
            // there is an `[any]` edge for it to belong to. A site that forgets to carry the state
            // is not a crash -- it is a silent budget refill -- so it is asserted rather than hoped.
            if (manager.anyUnroll.enabled) {
                check((anyId != null) == containsAnyAccessor()) {
                    "anyId/[any] edge mismatch: anyId=$anyId, accessors=${accessors?.toList()}"
                }
            }
        }

        init {
            var hash = 0L
            var depth = 0
            var containsStatic = false
            var containsAnyDeep = false

            if (isAbstract) hash += 1
            if (deepAccessorExclusion != null) hash += deepAccessorExclusion.hashCode().toLong() shl 3
            // Mixed in additively, like everything else here: nothing decodes `hash`, it is a bucket
            // key plus an equality prefilter. `anyId.id` is a dense counter rather than an identity
            // hash so it distributes inside a sum-of-children and adds no run-to-run variation.
            if (anyId != null) hash += anyId.id.toLong() shl 7

            if (isFinal) {
                depth = 1
                hash += 2
            }

            if (accessors != null) {
                containsStatic = accessors.any { it.isStaticAccessor() }
            }

            if (accessorNodes != null) {
                val accessorsHash = accessorNodes.sumOf { it.hash }
                hash += accessorsHash shl 5

                depth = accessorNodes.maxOf { it.maxDepth } + 1

                containsStatic = containsStatic || accessorNodes.any { it.containsStatic }
                containsAnyDeep = containsAnyDeep || accessorNodes.any { it.containsAnyInThisOrDeepNodes }
            }

            if (containsAnyAccessor()) {
                depth += ANY_ACCESSOR_DEPTH_CHARGE
                containsAnyDeep = true
            }

            this.hash = hash
            this.maxDepth = depth

            // The only place [flags] is written. The three constructed bits and the two derived
            // ones are packed together here so the field can stay a `val`, i.e. a final field.
            var packed = 0
            if (interned) packed = packed or INTERNED
            if (isAbstract) packed = packed or ABSTRACT
            if (isFinal) packed = packed or FINAL
            if (containsStatic) packed = packed or CONTAINS_STATIC
            if (containsAnyDeep) packed = packed or CONTAINS_ANY_DEEP
            this.flags = packed.toByte()
        }

        init {
            var size = 1L
            if (accessorNodes != null) {
                size += accessorNodes.sumOf { it.size }
            }
            this.size = size
        }

        override fun hashCode(): Int = hash.toInt()

        override fun equals(other: Any?): Boolean {
            if (this === other) return true
            if (other !is AccessNode) return false

            if (hash != other.hash) return false
            // Compare the IDENTITY bits one by one, NEVER `flags` as a whole: `interned` is storage
            // state, and `containsStatic` / `containsAnyInThisOrDeepNodes` are derived from the
            // children that `accessorNodes.contentEquals` already compares. Folding them into the
            // comparison would make structurally equal nodes unequal and break interning.
            if (isAbstract != other.isAbstract || isFinal != other.isFinal) return false
            if (deepAccessorExclusion != other.deepAccessorExclusion) return false
            // The STORED reference, never `find()` -- see [anyId]. Two nodes whose states have since
            // been unioned stay unequal; they are structural duplicates that the next rebuild
            // removes, which is cheaper than a hash that moves under a live entry.
            if (anyId !== other.anyId) return false

            if (!accessors.contentEquals(other.accessors)) return false
            return accessorNodes.contentEquals(other.accessorNodes)
        }

        /** Distinct nodes whose `isAbstract` is set -- the graft's candidate attachment points. */
        fun countAbstractNodes(): Int {
            val visited = IdentityHashMap<AccessNode, Unit>()
            var abstract = 0
            val stack = ArrayList<AccessNode>()
            stack.add(this)
            while (stack.isNotEmpty()) {
                val n = stack.removeLast()
                if (visited.put(n, Unit) != null) continue
                if (n.isAbstract) abstract++
                n.forEachAccessor { _, c -> stack.add(c) }
            }
            return abstract
        }

        fun countNodes(visited: IdentityHashMap<AccessNode, Unit> = IdentityHashMap()): Int {
            visited[this] = Unit
            forEachAccessor { _, node ->
                node.countNodes(visited)
            }
            return visited.size
        }

        override fun toString(): String = buildString { print(this) }

        fun print(builder: StringBuilder, prefix: String = "", suffix: String = ""): Unit = with(builder) {
            if (isFinal || isAbstract) {
                append(prefix)

                if (isFinal) {
                    appendLine(FinalAccessor.toSuffix())
                } else {
                    val annotation = deepAccessorExclusion?.toString().orEmpty()
                    appendLine("/*$annotation$suffix")
                }
            }

            forEachAccessor { fieldIdx, child ->
                val field = with(manager) { fieldIdx.accessor }
                child.print(builder, prefix + field.toSuffix())
            }
        }

        inline fun forEachAccessor(body: (AccessorIdx, AccessNode) -> Unit) {
            if (accessors != null) {
                for (i in accessors.indices) {
                    body(accessors[i], accessorNodes!![i])
                }
            }
        }

        val isEmpty: Boolean
            get() = !isAbstract && !isFinal && accessors == null

        val isEmptyAbstract: Boolean
            get() = isAbstract && !isFinal && accessors == null

        /**
         * Whether anything at all hangs below this node.
         *
         * This is the property a taint mark requires of the node under it: a mark is a leaf marker,
         * so nothing structured -- an `[any]` least of all -- may sit below it. The raw
         * [Companion.create] choke point enforces exactly this, which is the weakest condition that
         * still gives the invariant, so it cannot reject a legitimate shape such as an abstract leaf
         * carrying a [DeepAccessorExclusion] claim.
         *
         * Consequence: `[any].![m].[any]` is unconstructible. That is what lets [prependAnyAccessor]
         * collapse a nested `[any]` without carving out an exception for an intervening uncovered
         * accessor of taint-mark kind -- an `[any]` can never sit below a mark to begin with.
         */
        val isStructurelessLeaf: Boolean
            get() = accessors == null

        /**
         * The stricter rule [addParentIfPossible] applies when PREPENDING a mark: only the three
         * manager singletons qualify. It implies [isStructurelessLeaf] and is kept separate so that
         * tightening the prepend rule and tightening the construction invariant stay independent
         * decisions.
         */
        val isLegalNodeBelowTaintMark: Boolean
            get() = this == manager.finalNode || this == manager.abstractNode || this == manager.abstractFinalNode

        private fun accessorIndex(accessor: AccessorIdx): Int {
            if (accessors == null) return -1
            return accessors.binarySearch(accessor)
        }

        private fun getNodeByAccessor(accessor: AccessorIdx): AccessNode? =
            accessorNodes?.getOrNull(accessorIndex(accessor))

        fun containsAnyAccessor(): Boolean =
            accessorIndex(ANY_ACCESSOR_IDX) >= 0

        fun contains(accessor: AccessorIdx): Boolean {
            if (accessor == FINAL_ACCESSOR_IDX) return isFinal

            val accessorIdx = accessorIndex(accessor)
            if (accessorIdx >= 0) return true

            val anyAccessorNode = getNodeByAccessor(ANY_ACCESSOR_IDX)
                ?: return false

            if (anyAccessorNode.contains(accessor)) return true

            return with(manager) {
                anyAccessorUnrollStrategy.unrollAccessor(accessor.accessor)
            }
        }

        /**
         * [receiver] `mergeAdd` [arrival], tolerating either side being null.
         *
         * The parameters are named rather than positional-by-convention because the body INVERTS
         * them: the SECOND argument is the receiver. Written as `l`/`r` this reads as
         * receiver/argument and does the opposite, so a new call site written on the obvious
         * assumption gets the arrival as receiver -- and the receiver is what `union` keeps the
         * representative of, so that mistake costs an extra fixpoint lap on every folded loop in the
         * program rather than producing a wrong answer.
         */
        private fun mergeAddMaybeNull(arrival: AccessNode?, receiver: AccessNode?): AccessNode? {
            if (arrival == null)
                return receiver
            if (receiver == null)
                return arrival
            return receiver.mergeAdd(arrival)
        }

        /**
         * The QUERY entry point: answers what the fact denotes without moving any budget.
         *
         * Its callers ([equalTo], [containsStrict], [containsThroughAny], and the premise side's
         * `matchThroughAny` / `splitDeltaStrict`) decide a boolean; charging them would trip the cut
         * early and coarsen facts that were never growing. Misclassifying a build as a query is the
         * dangerous direction -- that is a refill -- so the split is a second entry point rather
         * than a flag, and the two lists are short enough to check by reading them.
         */
        fun getChild(accessor: AccessorIdx): AccessNode? = getChild(accessor, record = false)

        /**
         * The BUILD entry point: [getChild] plus the R4 record.
         *
         * Used by every caller whose result becomes part of a fact -- the two `readAccessor`s,
         * [AccessTree.delta] and [filterStartsWith].
         */
        fun getChildRecording(accessor: AccessorIdx): AccessNode? = getChild(accessor, record = true)

        private fun getChild(accessor: AccessorIdx, record: Boolean): AccessNode? {
            if (accessor == FINAL_ACCESSOR_IDX) return manager.finalNode.takeIf { this.isFinal }

            val node = getNodeByAccessor(accessor)

            val anyAccessorNode = getNodeByAccessor(ANY_ACCESSOR_IDX)
                ?: return node

            val anyChild = anyAccessorNode.getNodeByAccessor(accessor)
            var resultNode = mergeAddMaybeNull(anyChild, node)

            if (manager.isCoveredByAny(accessor)) {
                // The unique point at which a concrete accessor is SYNTHESISED out of an `[any]`, as
                // opposed to being read off an edge the fact literally has. Putting the record here
                // covers every caller at once, which is the structural difference from a predicate
                // keyed on one caller's tree shapes.
                //
                // The arm destroys the `[any]` edge and rebuilds it, so the returned `[any]` is a
                // FRESH node -- which is what makes the automaton expressible: the fresh edge takes
                // the successor state while the original keeps its own. Had the arm returned the
                // original node the two would be forced to share a state.
                val childState = if (record) {
                    manager.anyUnroll.readChild(anyId, accessor)
                } else {
                    manager.anyUnroll.peekChild(anyId, accessor)
                }

                val anyAccessorNoRepeats = anyAccessorNode.clearChild(accessor)
                val originalAnyNoRepeats =
                    anyAccessorNoRepeats.addParentIfPossible(ANY_ACCESSOR_IDX, childState ?: anyId)
                resultNode = mergeAddMaybeNull(originalAnyNoRepeats, resultNode)

                if (ApOpDiagnostics.enabled) {
                    // Read back by `delta`, which is the caller that turns this into a round trip.
                    ApOpDiagnostics.crossedAnyFlag.get().value++
                    val literal = node?.size ?: 0L
                    val result = resultNode?.size ?: 0L
                    ApOpDiagnostics.anyReadCalls.incrementAndGet()
                    ApOpDiagnostics.anyReadLiteralNodes.addAndGet(literal)
                    ApOpDiagnostics.anyReadResultNodes.addAndGet(result)
                    if (node == null) ApOpDiagnostics.anyReadFromNothing.incrementAndGet()
                    if (result > literal) {
                        ApOpDiagnostics.anyReadGrew.incrementAndGet()
                        ApOpDiagnostics.anyReadGrowth.addAndGet(result - literal)
                        ApOpDiagnostics.example("B-getChildAny", result - literal) {
                            "read " + with(manager) { accessor.accessor }.toSuffix() +
                                " off a node that owns an [any]: literal=" + literal +
                                " -> returned=" + result + "; owner=" +
                                this.toString().replace('\n', ' ')
                        }
                    }
                }
            }

            return resultNode
        }

        /**
         * @param absorbing whether a covered accessor may be absorbed into an `[any]` at the root of
         *   this node instead of being written above it. Only the ELEMENT and FIELD arms can absorb;
         *   the rest carry uncovered accessors, which the rule declines to touch anyway. The one
         *   caller that passes `false` is the initial-fact abstraction, which prepends exactly the
         *   accessor it just read.
         */
        fun addParentIfPossible(
            accessor: AccessorIdx,
            anyState: AnyUnrollState? = null,
            absorbing: Boolean = true,
        ): AccessNode? {
            if (containsStatic) return null

            if (!absorbing && AnyUnrollDiagnostics.enabled && manager.anyUnroll.enabled) {
                // What the exclusion actually saved. A "must stay zero" counter here would be
                // guaranteed zero by construction -- the funnel is unreachable from the excluded
                // caller -- and would therefore say nothing.
                if (absorbTargetFor(accessor, this, count = false) != null) {
                    AnyUnrollDiagnostics.tifaAbsorbSuppressed.incrementAndGet()
                }
            }

            return when {
                accessor == FINAL_ACCESSOR_IDX -> null
                accessor == ELEMENT_ACCESSOR_IDX -> manager.create(
                    elementAccess = limitElementAccess(limit = SUBSEQUENT_ARRAY_ELEMENTS_LIMIT),
                    absorbing = absorbing,
                )
                accessor.isFieldAccessor() -> addParentFieldAccess(accessor, absorbing)
                accessor.isStaticAccessor() -> create(accessor, this)
                accessor == VALUE_ACCESSOR_IDX -> {
                    if (accessors?.any { !it.isTaintMarkAccessor() } == true) {
                        return null
                    }

                    create(accessor, this)
                }

                accessor.isTaintMarkAccessor() -> {
                    if (isLegalNodeBelowTaintMark) {
                        create(accessor, this)
                    } else {
                        null
                    }
                }

                accessor == ANY_ACCESSOR_IDX -> prependAnyAccessor(anyState)

                accessor == TYPE_INFO_GROUP_ACCESSOR_IDX -> create(accessor, this)
                accessor.isTypeInfoAccessor() -> create(accessor, this)

                else -> error("Unsupported accessor: $accessor")
            }
        }

        fun equalTo(otherAccess: AccessPath.AccessNode?): Boolean {
            if (otherAccess == null) {
                return isEmptyAbstract
            }

            var node = this
            otherAccess.toList().forEachInt { accessor ->
                if (accessor == FINAL_ACCESSOR_IDX) {
                    return node.isFinal && node.accessors == null
                }

                if (node.accessors?.size != 1) return false
                node = node.getChild(accessor) ?: return false
            }

            return node.isEmptyAbstract
        }

        fun contains(otherAccess: AccessPath.AccessNode?): Boolean {
            if (containsStrict(otherAccess)) return true
            if (otherAccess == null || !otherAccess.containsAnyAccessor()) return false
            return containsThroughAny(otherAccess, intArrayOf(CONTAINS_THROUGH_ANY_STEP_LIMIT))
        }

        private fun containsStrict(otherAccess: AccessPath.AccessNode?): Boolean {
            if (otherAccess == null) {
                return isAbstract
            }

            var node = this
            otherAccess.toList().forEachInt { accessor ->
                if (accessor == FINAL_ACCESSOR_IDX) return node.isFinal
                node = node.getChild(accessor) ?: return false
            }
            return node.isAbstract
        }

        /**
         * The permissive re-run of [contains] for a PREMISE that carries an `[any]`.
         *
         * The strict walk above treats every premise accessor as one literal link, `[any]`
         * included: it asks the fact for a child under `ANY_ACCESSOR_IDX` and, having consumed the
         * premise, insists the fact be abstract there. That is right for summary APPLICATION -- and
         * `AccessTree.delta`, which decides it, is deliberately left alone -- but it is wrong here.
         * `[any]` is zero-or-more covered steps, so a premise `X.[any].![m]` is answered by a fact
         * `X.![m].*` (zero steps) and by `X.f.![m].*` (one step) just as much as by `X.[any].![m].*`,
         * and a premise ending in `[any]` is `X.[any].*`, which under the zero-or-more reading is
         * simply `X.*` -- everything below `X`.
         *
         * The only callers of [FinalFactAp.contains] are in `MethodTraceResolver`, which ATTRIBUTES
         * an already-decided finding to a summary edge. Under-matching there does not cost trace
         * precision, it costs whole findings: `TracePath` turns a missing trace into a
         * `TracePathGenerationResult.Failure` and `TaintAnalyzer.fullScan` drops exactly those. So
         * this runs only after the strict walk has already said no, and can only add matches.
         *
         * [budget] is a one-cell visit counter. The `[any]` arm branches over every covered child,
         * so the search is worst-case exponential in the fact's breadth; running out reports NO
         * match, which is exactly what this premise got before the arm existed.
         */
        private fun containsThroughAny(otherAccess: AccessPath.AccessNode?, budget: IntArray): Boolean {
            if (budget[0]-- <= 0) return false

            if (otherAccess == null) return isAbstract

            val accessor = otherAccess.accessor
            if (accessor == FINAL_ACCESSOR_IDX) return isFinal

            if (accessor != ANY_ACCESSOR_IDX) {
                val child = getChild(accessor) ?: return false
                return child.containsThroughAny(otherAccess.next, budget)
            }

            // `X.[any]` with nothing below it is `X.[any].*` == `X.*`: whatever hangs here is covered.
            val next = otherAccess.next ?: return true

            // zero steps
            if (containsThroughAny(next, budget)) return true

            // one or more steps, through the fact's own `[any]` link or through any covered child
            forEachAccessor { childAccessor, childNode ->
                if (childAccessor != ANY_ACCESSOR_IDX && !manager.isCoveredByAny(childAccessor)) {
                    return@forEachAccessor
                }
                if (childNode.containsThroughAny(otherAccess, budget)) return true
            }

            return false
        }

        sealed interface MatchResult {
            data object NotMatched : MatchResult
            data class MatchedWithRemainder(val remainder: AccessNode?) : MatchResult
        }

        fun splitOnMatching(otherAccess: AccessPath.AccessNode?): MatchResult  {
            if (otherAccess == null) {
                if (!isAbstract || deepAccessorExclusion != null) return MatchResult.NotMatched

                val remainder = removeAbstraction().takeIf { !it.isEmpty }
                return MatchResult.MatchedWithRemainder(remainder)
            }

            val accessorsOnPath = otherAccess.toList()

            var node = this
            accessorsOnPath.forEachInt { accessor ->
                if (accessor == FINAL_ACCESSOR_IDX) {
                    if (!node.isFinal) return MatchResult.NotMatched

                    val remainder = this.reconstructRemainder(accessorsOnPath, idx = 0)
                    return MatchResult.MatchedWithRemainder(remainder)
                }

                node = node.getNodeByAccessor(accessor)
                    ?: return MatchResult.NotMatched
            }

            if (!node.isAbstract || node.deepAccessorExclusion != null) return MatchResult.NotMatched

            val remainder = this.reconstructRemainder(accessorsOnPath, idx = 0)
            return MatchResult.MatchedWithRemainder(remainder)
        }

        private fun reconstructRemainder(accessors: IntList, idx: Int): AccessNode? {
            if (idx == accessors.size) {
                return removeAbstraction().takeIf { !it.isEmpty }
            }

            val accessor = accessors.getInt(idx)

            val levelRemainder = clearChild(accessor)
                .takeIf { !it.isEmpty }

            if (accessor == FINAL_ACCESSOR_IDX) {
                return levelRemainder
            }

            val childRemainder = getNodeByAccessor(accessor)
                ?.reconstructRemainder(accessors, idx + 1)
                ?.takeIf { !it.isEmpty }
                // Same raw re-creation as the spine fold above: carry the state of the edge this
                // frame walked through.
                ?.let { create(accessor, it, anyId) }

            if (levelRemainder == null) return childRemainder
            if (childRemainder == null) return levelRemainder
            return levelRemainder.mergeAdd(childRemainder)
        }

        fun addParent(accessor: AccessorIdx, anyState: AnyUnrollState? = null): AccessNode =
            addParentIfPossible(accessor, anyState)
                ?: error("Impossible accessor")

        /**
         * Install [accessor] above this node, absorbing it into an `[any]` at this node's root when
         * that `[any]` is no longer entitled to carry a concrete step above it.
         *
         * `a.[any].R` is a subset of `[any].R` for covered `a`, so declining to write the step
         * asserts MORE, not less: absorption, not truncation, and no configuration can lose a
         * finding relative to no limit at all -- GIVEN the subtree probe below.
         *
         * **Which state the surviving `[any]` takes is where this differs from a budget-only form.**
         * Moving to the PREDECESSOR makes the absorption the exact inverse of the read that bought
         * the accessor, so a delta/concat round trip returns the fact to the state it started from
         * and the fixed point closes. Keeping the state would bound the DEPTH while leaving every lap
         * tagged with a different state, i.e. a different node, i.e. more work. The shipped absorb
         * kept the state, at a site whose caller had the predecessor in hand three lines away.
         *
         * Two traps. The SPLIT: this node is generally a MERGE of the `[any]` branch and concrete
         * branches, and dropping the step across the whole node rewrites `a.f.S` as `f.S` on the
         * concrete ones -- neither superset nor subset. The SUBTREE PROBE: `getChild`'s covered arm
         * returns `anyAccessorNode.clearChild(a)`, so it drops `SIGMA*.a.L(R_a)` and reading `a` off
         * `[any].R` is a NARROWING; a narrowing means a coarser fact can answer a read with LESS, so
         * absorbing `a` into an `[any]` whose subtree already has an `a` child loses those paths on
         * the next read. With no `a` child the dropped term is empty and the read after the rewrite
         * equals the read before it. The condition is on the SUBTREE rather than an appeal to
         * `limitFieldAccess` -- that limiter cuts every occurrence of a field at any depth, `[any]`
         * included, so `a.[any].a...` is unconstructible for fields, but `limitElementAccess` caps
         * only CONSECUTIVE element runs and `[].[any].[]` is not consecutive.
         *
         * **Guard order is load-bearing.** The first four are O(1) field and array probes and are the
         * overwhelmingly common exits; `isCoveredByAny` is last because it delegates straight to the
         * injected strategy, and the one installed for the whole prescan phase THROWS rather than
         * returning false.
         */
        private fun installAbove(accessor: AccessorIdx, anyState: AnyUnrollState?): AccessNode {
            // A `CREDIT` position with no incoming edge on this accessor ANYWHERE IN IT: the step did
            // not come out of this `[any]`, and keeping it is the whole point of the targeting. A
            // SELF-LOOP is not that case -- `pred` is then non-null and is the state itself, and the
            // step is absorbed in place.
            val pred = absorbTargetFor(accessor, this) ?: return createRaw(accessor, this, anyState)
            val anyNode = getNodeByAccessor(ANY_ACCESSOR_IDX)!!

            if (AnyUnrollDiagnostics.enabled) {
                AnyUnrollDiagnostics.absorptions.incrementAndGet()
                if (accessor == ELEMENT_ACCESSOR_IDX) {
                    AnyUnrollDiagnostics.elementPrependOverAny.incrementAndGet()
                }
            }

            val absorbed = createRaw(ANY_ACCESSOR_IDX, anyNode, pred)
            val rest = clearChild(ANY_ACCESSOR_IDX).takeIf { !it.isEmpty } ?: return absorbed
            return createRaw(accessor, rest).mergeAdd(absorbed)
        }

        fun removeAbstraction(): AccessNode =
            recreate(isAbstract = false, isFinal, deepAccessorExclusion = null, accessors, accessorNodes)

        /**
         * [absorbedAnyStep] is C2 of the concat absorption: [DeepAccessorExclusion] is
         * DEPTH-RELATIVE, and absorption hoists accessors upward, so a `![m]` that stood at depth 4
         * arrives here as a START accessor. When at least one step was consumed every surviving
         * accessor is logically at depth >= 1, so the depth-1 set must also be applied with
         * `keepStartAccessor = false` -- otherwise the start exemption silently frees a mark the
         * sanitizer had claimed. When nothing was consumed the behaviour is exactly as before.
         *
         * Applying the depth-1 set at the start is strictly MORE aggressive filtering, i.e. more
         * precise and in the sound direction.
         */
        private fun AccessNode.filterDeepExclusion(
            deepAccessorExclusion: DeepAccessorExclusion?,
            absorbedAnyStep: Boolean,
        ): AccessNode? {
            if (deepAccessorExclusion == null) return this

            var filtered: AccessNode = this
            deepAccessorExclusion.accessorsFromDepth0.forEach {
                filtered = filtered.clearAllAccessorOccurrences(it, keepStartAccessor = false, cache = IdentityHashMap()) ?: return null
            }
            deepAccessorExclusion.accessorsFromDepth1.forEach {
                filtered = filtered.clearAllAccessorOccurrences(it, keepStartAccessor = !absorbedAnyStep, cache = IdentityHashMap()) ?: return null
            }

            val belowClaim = deepAccessorExclusion.collapseToDepth0()
            val cache = IdentityHashMap<AccessNode, AccessNode>()
            var annotated = filtered.transformAccessors { _, node ->
                node.annotateAbstractNodes(belowClaim, cache)
            }
            if (annotated.isAbstract) {
                val merged = DeepAccessorExclusion.merge(annotated.deepAccessorExclusion, deepAccessorExclusion)
                annotated = annotated.updateDeepExclusion(merged)
            }
            return annotated
        }

        /** Build `[any].this`. The normalisation and the manager rules both live in [createAnyEdge]. */
        private fun prependAnyAccessor(anyState: AnyUnrollState?): AccessNode =
            createAnyEdge(this, anyState, AnyUnrollManager.MINT_PREPEND)

        /**
         * Normalise this node for the position DIRECTLY UNDER an `[any]` edge, and report the union
         * of every `[any]` manager state found in it.
         *
         * Two jobs, and the second is unconditional while the first is not.
         *
         * **Collapse where legal.** `[any]` is `sigma*` for the covered accessors `sigma`, so
         * `sigma* ⊇ sigma*.f.sigma*` for covered `f` -- a monotone coarsening, NOT the identity the
         * older KDoc here claimed. Sound, because a superset of a taint fact can only add false
         * positives, but it has a precision cost, which is why it is measurable on its own
         * (`-Dopentaint.anyCollapseNested=false`). The containment needs `f` covered: for an
         * uncovered `f` it fails outright and collapsing would LOSE flows.
         *
         * **Union always.** Two `[any]` edges on one root-to-leaf path multiply -- the outer
         * materialises up to `L` prefixes and each carries a copy of the inner, so the population
         * under one origin is `L^d` rather than `L`. That is the exact failure the per-fact carried
         * limit was rejected for, so the branch invariant is a manager-level obligation in its own
         * right and holds whether or not the tree collapses the two edges.
         *
         * The [containsAnyInThisOrDeepNodes] gate keeps the overwhelmingly common case O(1); the
         * flag is a final field set in the child's own init block, so it is readable BEFORE the
         * parent exists, which is what makes enforcement at construction possible at all.
         */
        private fun normaliseUnderAny(): Pair<AccessNode, AnyUnrollState?> {
            if (!containsAnyInThisOrDeepNodes) return this to null
            // The walk below asks `isCoveredByAny` about every child, and the prescan's strategy
            // THROWS rather than answering. Nothing legitimate reaches here in that phase -- the
            // contract is that no `[any]` exists -- but deserialisation is the one `[any]` source
            // that never consults the strategy, and a stale summary blob would otherwise take down
            // the prescan through a code path that used to be unreachable from the factory.
            if (!manager.anyAccessorsQueryable) return this to null

            val states = mutableListOf<AnyUnrollState>()

            if (!COLLAPSE_NESTED_ANY) {
                collectAnyStates(states, IdentityHashMap())
                return this to unionStates(states)
            }

            if (AnyUnrollDiagnostics.enabled) AnyUnrollDiagnostics.collapses.incrementAndGet()

            // Every `[any]` subtree found on a covered-only path is hoisted to sit directly under
            // the new `[any]`, and must itself be stripped there -- hence the worklist.
            val pending = ArrayDeque<AccessNode>()
            val enqueued = IdentityHashMap<AccessNode, Unit>()
            val cache = IdentityHashMap<AccessNode, AccessNode?>()

            pending.addLast(this)
            enqueued[this] = Unit

            var nextNode: AccessNode? = null
            while (pending.isNotEmpty()) {
                val stripped = pending.removeFirst().stripAnyBelowCoveredPath(pending, enqueued, cache, states)
                if (stripped != null) {
                    nextNode = nextNode?.mergeAdd(stripped) ?: stripped
                }
            }

            return (nextNode ?: manager.emptyNode) to unionStates(states)
        }

        /**
         * Delete every `[any]` edge reachable from this node through covered-only accessors,
         * enqueueing each deleted edge's subtree onto [pending] so it can be merged in directly
         * under the new `[any]`. Returns null when nothing is left of this branch.
         *
         * Every enqueued node is a node of the original tree, so the worklist is finite.
         */
        private fun stripAnyBelowCoveredPath(
            pending: ArrayDeque<AccessNode>,
            enqueued: IdentityHashMap<AccessNode, Unit>,
            cache: IdentityHashMap<AccessNode, AccessNode?>,
            states: MutableList<AnyUnrollState>,
        ): AccessNode? {
            if (!containsAnyInThisOrDeepNodes) return this
            if (cache.containsKey(this)) return cache[this]

            manager.cancellation.checkpoint()

            // This node's own `[any]` edge, if it has one, is deleted by the ANY arm below, so its
            // state is one of the ones the new edge above must absorb.
            anyId?.let { states.add(it) }

            val result = transformAccessorsNonEmpty { accessor, node ->
                when {
                    accessor == ANY_ACCESSOR_IDX -> {
                        if (enqueued.put(node, Unit) == null) {
                            pending.addLast(node)
                        }
                        null
                    }

                    manager.isCoveredByAny(accessor) ->
                        node.stripAnyBelowCoveredPath(pending, enqueued, cache, states)

                    else -> {
                        // Union without collapsing. Reachable only for `[any].<uncovered>.[any]`,
                        // which the analyzer is not believed to build -- marks are enforced by the
                        // structureless-leaf check, statics by the subtree-wide containsStatic
                        // guard, `[final]` is not an edge and `[value]` is dead code, and type-info
                        // now has its own check. The counter is what keeps that a measurement.
                        if (node.containsAnyInThisOrDeepNodes) {
                            countUnionWithoutCollapse(accessor)
                            node.collectAnyStates(states, IdentityHashMap())
                        }
                        node
                    }
                }
            }

            cache[this] = result
            return result
        }

        /** Every manager state in this subtree, without touching the tree. */
        private fun collectAnyStates(dst: MutableList<AnyUnrollState>, visited: IdentityHashMap<AccessNode, Unit>) {
            if (!containsAnyInThisOrDeepNodes) return
            if (visited.put(this, Unit) != null) return

            anyId?.let { dst.add(it) }
            forEachAccessor { _, child -> child.collectAnyStates(dst, visited) }
        }

        private fun unionStates(states: List<AnyUnrollState>): AnyUnrollState? {
            if (states.isEmpty()) return null
            var acc: AnyUnrollState? = states[0]
            for (i in 1 until states.size) {
                acc = manager.anyUnroll.union(acc, states[i])
            }
            return acc
        }

        private fun countUnionWithoutCollapse(accessor: AccessorIdx) {
            if (!AnyUnrollDiagnostics.enabled) return
            when {
                accessor.isTaintMarkAccessor() -> AnyUnrollDiagnostics.unionWithoutCollapseMark
                accessor.isStaticAccessor() -> AnyUnrollDiagnostics.unionWithoutCollapseStatic
                accessor.isTypeInfoAccessor() || accessor == TYPE_INFO_GROUP_ACCESSOR_IDX ->
                    AnyUnrollDiagnostics.unionWithoutCollapseTypeInfo
                else -> AnyUnrollDiagnostics.unionWithoutCollapseOther
            }.incrementAndGet()
        }

        /**
         * Re-label THIS node's own `[any]` edge with [state], leaving the shape alone.
         *
         * The unroll re-parents an entire node under one more concrete accessor, so the `[any]` edge
         * survives the operation while its language loses a step -- which is exactly a successor in
         * the automaton. Only the top edge is touched; deeper and sibling `[any]`s keep their own
         * states, because only this one's language changed.
         */
        fun withAnyState(state: AnyUnrollState?): AccessNode {
            if (!manager.anyUnroll.enabled) return this
            if (!containsAnyAccessor()) return this
            if (state == null || state === anyId) return this
            return manager.create(isAbstract, isFinal, deepAccessorExclusion, accessors, accessorNodes, state)
        }

        /**
         * Rebuild this node with a new accessor set, carrying its own `[any]` state -- and dropping
         * it exactly when the new set no longer holds an `[any]` edge.
         *
         * This is the "keeps or shrinks the accessor array" row of the propagation rule. Sites that
         * GROW the array (the merges, the bulk add) must compute the union explicitly instead.
         */
        internal fun recreate(
            isAbstract: Boolean,
            isFinal: Boolean,
            deepAccessorExclusion: DeepAccessorExclusion?,
            accessors: IntArray?,
            accessorNodes: Array<AccessNode>?,
        ): AccessNode = manager.create(
            isAbstract, isFinal, deepAccessorExclusion, accessors, accessorNodes,
            anyStateIfPresent(accessors, anyId),
        )

        /**
         * Consume the longest prefix of this delta that an `[any]` edge sitting DIRECTLY above it
         * already denotes, and report whether anything was consumed.
         *
         * ```
         * [any].*  (+)  x.y.z.![m].$  ->  [any].![m].$
         * [any].*  (+)  x.y.z.*       ->  [any].*        (fully covered, still abstract)
         * [any].*  (+)  ![m].$        ->  [any].![m].$   (nothing to consume)
         * [any].*  (+)  x.[any].![m].$ -> [any].![m].$   (a nested `[any]` is consumable too)
         * ```
         *
         * The delta is a TREE, not a chain, so "consume the prefix" means: merge into the root every
         * child reached through a consumable accessor, delete that edge, and iterate to a fixpoint.
         * Children reached through an accessor `[any]` does not cover stay exactly where they are.
         *
         * Sound under both readings of `[any]` (design 3.4): existentially, `w.x.y.z` is itself a
         * covered sequence, so the absorbed fact denotes a SUPERSET; universally, instantiating the
         * quantifier at `w := w'.x.y.z` shows the absorbed fact is the stronger assertion. Either
         * way it is a monotone coarsening -- never a loss on any branch.
         *
         * The predicate is `[any]` itself OR [TreeApManager.isCoveredByAny], not
         * `AnyAccessor.containsAccessor`: the injected [AnyAccessorUnrollStrategy] is the operative
         * denotation of `[any]` for this backend, and it can be narrower. Admitting a nested `[any]`
         * is C3 -- `isCoveredByAny(ANY_ACCESSOR_IDX)` is false, yet `[any].[any]` denotes a subset
         * of `[any]`, and stopping there would rebuild exactly the nested shape 5.2 collapses.
         *
         * Terminates: every merge-up strictly reduces the summed length of the tree's paths (each
         * path through the deleted edge loses a step, no path is created), and the tree is finite.
         */
        private fun absorbCoveredByAnyPrefix(): Pair<AccessNode, Boolean> {
            var current = this
            var absorbedAnyStep = false

            while (true) {
                val accessors = current.accessors ?: break

                var consumedIdx = -1
                for (i in accessors.indices) {
                    val accessor = accessors[i]
                    if (accessor == ANY_ACCESSOR_IDX || manager.isCoveredByAny(accessor)) {
                        consumedIdx = i
                        break
                    }
                }

                if (consumedIdx < 0) break

                manager.cancellation.checkpoint()

                val consumedAccessor = accessors[consumedIdx]
                val consumedNode = current.accessorNodes!![consumedIdx]

                // The delta's own `[any]` edge is being eaten by the `[any]` sitting directly above
                // this node. `removeSingleAccessor` drops the state with the edge, so union it into
                // whatever `[any]` survives in the result first. When the consumed subtree carries
                // one, that is where the pot lives on; when it does not, the record is genuinely
                // lost, which is sound (the remaining budget only goes further) but means `total` is
                // a lower bound on what was materialised.
                if (consumedAccessor == ANY_ACCESSOR_IDX) {
                    manager.anyUnroll.union(consumedNode.anyId, current.anyId)
                }

                // C1: never "nothing to graft". [mergeAdd] unions isAbstract/isFinal and intersects
                // deepAccessorExclusion -- exactly the join wanted -- so a fully covered branch
                // collapses to a node that still CARRIES its leaf's flags. Returning an empty node
                // here would leave the graft with concatNode == null, the abstraction unrestored,
                // and `takeIf { !it.isEmpty }` would drop the whole branch: lost taint.
                current = current.removeSingleAccessor(consumedAccessor).mergeAdd(consumedNode)
                absorbedAnyStep = true
            }

            return current to absorbedAnyStep
        }

        private fun limitElementAccess(limit: Int): AccessNode {
            if (limit > 0) {
                return transformAccessors { accessor, accessNode ->
                    if (accessor == ELEMENT_ACCESSOR_IDX) {
                        accessNode.limitElementAccess(limit - 1)
                    } else {
                        accessNode
                    }
                }
            }

            return collapseElementAccess().also {
                check(it.getNodeByAccessor(ELEMENT_ACCESSOR_IDX) == null) {
                    "Array element limit invariant failure"
                }
            }
        }

        private fun collapseElementAccess(): AccessNode {
            val elementAccess = getNodeByAccessor(ELEMENT_ACCESSOR_IDX) ?: return this

            val collapsedElementAccess = elementAccess.collapseElementAccess()
            val result = removeSingleAccessor(ELEMENT_ACCESSOR_IDX)
            return result.mergeAdd(collapsedElementAccess)
        }

        private fun addParentFieldAccess(
            newRootField: AccessorIdx,
            absorbing: Boolean = true,
        ): AccessNode {
            val filteredNodes = mutableListOf<IntObjectImmutablePair<AccessNode>>()
            val limitedThis = limitFieldAccess(newRootField, filteredNodes)

            // The hottest covered prepend in the engine: `limitedThis` routinely owns an `[any]`,
            // because `limitFieldAccessCached` recurses through every child, `ANY_ACCESSOR_IDX`
            // included, stripping only `newRootField`. Reached from the public `prependAccessor`,
            // hence Cleaner, AliasUtil, RulePreconditionUtils and the initial-fact abstraction.
            val resultNode = if (limitedThis != null) {
                if (absorbing) create(newRootField, limitedThis) else createRaw(newRootField, limitedThis)
            } else {
                manager.emptyNode
            }

            // limitFieldAccess only ever extracts entries keyed by a FIELD accessor, so no `[any]`
            // edge can arrive through this list -- the comment is about the entry LIST, not about the
            // `create` above.
            return resultNode.bulkMergeAddAccessors(filteredNodes, entryAnyState = null, absorbing = absorbing)
                .also { check(!it.isEmpty) { "Empty node after field normalization" } }
        }

        fun clearChild(accessor: AccessorIdx): AccessNode = when (accessor) {
            FINAL_ACCESSOR_IDX -> recreate(isAbstract, isFinal = false, deepAccessorExclusion, accessors, accessorNodes)
            else -> removeSingleAccessor(accessor)
        }

        fun filter(exclusion: ExclusionSet.Concrete): AccessNode {
            val isFinal = this.isFinal && FinalAccessor !in exclusion

            val transformedAccessors = transformAccessors(accessors, accessorNodes) { accessor, node ->
                with(manager) {
                    node.takeIf { accessor.accessor !in exclusion }
                }
            }

            if (isFinal == this.isFinal && transformedAccessors == null) {
                return this
            }

            val accessors = transformedAccessors?.first ?: accessors
            val accessorNodes = transformedAccessors?.second ?: accessorNodes

            return recreate(isAbstract, isFinal, deepAccessorExclusion, accessors, accessorNodes)
        }

        fun clearAllAccessorOccurrences(
            accessorIdx: AccessorIdx,
            keepStartAccessor: Boolean,
            retainDeepAccessorExclusions: Boolean = true,
            cache: IdentityHashMap<AccessNode, AccessNode?>,
        ): AccessNode? {
            val transformed = transformAccessorsNonEmpty { currentAccessorIdx, node ->
                if (keepStartAccessor || currentAccessorIdx != accessorIdx) {
                    node.clearAccessorOccurrencesBelow(accessorIdx, retainDeepAccessorExclusions, cache)
                } else {
                    null
                }
            }

            return transformed?.let {
                if (retainDeepAccessorExclusions) {
                    it.annotateAnyFieldAccessorExclusion(accessorIdx, keepStartAccessor)
                } else {
                    it.updateDeepExclusion(null)
                }
            }
        }

        private fun clearAccessorOccurrencesBelow(
            accessorIdx: AccessorIdx,
            retainDeepAccessorExclusions: Boolean,
            cache: IdentityHashMap<AccessNode, AccessNode?>,
        ): AccessNode? {
            if (cache.containsKey(this)) return cache[this]
            manager.cancellation.checkpoint()

            val transformed = transformAccessorsNonEmpty { currentAccessorIdx, node ->
                if (currentAccessorIdx == accessorIdx) null
                else node.clearAccessorOccurrencesBelow(accessorIdx, retainDeepAccessorExclusions, cache)
            }

            val result = transformed?.let {
                if (retainDeepAccessorExclusions) {
                    it.annotateAnyFieldAccessorExclusion(accessorIdx, keepCurrentNodeAccessor = false)
                } else {
                    it.updateDeepExclusion(null)
                }
            }

            cache[this] = result
            return result
        }

        private fun annotateAnyFieldAccessorExclusion(accessorIdx: AccessorIdx, keepCurrentNodeAccessor: Boolean): AccessNode {
            if (!isAbstract) return this

            val annotated = if (keepCurrentNodeAccessor) {
                deepAccessorExclusion.addAccessorFromDepth1(accessorIdx)
            } else {
                deepAccessorExclusion.addAccessorFromDepth0(accessorIdx)
            }

            return updateDeepExclusion(annotated)
        }

        private fun updateDeepExclusion(annotation: DeepAccessorExclusion?) =
            if (annotation == deepAccessorExclusion) {
                this
            } else {
                recreate(isAbstract, isFinal, annotation, accessors, accessorNodes)
            }

        fun abstractOnly(): AccessNode =
            recreate(isAbstract = true, isFinal = false, deepAccessorExclusion, accessors = null, accessorNodes = null)

        fun annotateAbstractNodes(
            incoming: DeepAccessorExclusion,
            cache: IdentityHashMap<AccessNode, AccessNode>,
        ): AccessNode {
            cache[this]?.let { return it }

            manager.cancellation.checkpoint()

            val transformed = transformAccessors { _, node ->
                node.annotateAbstractNodes(incoming, cache)
            }

            val result = if (!transformed.isAbstract) {
                transformed
            } else {
                val merged = DeepAccessorExclusion.merge(transformed.deepAccessorExclusion, incoming)
                transformed.updateDeepExclusion(merged)
            }

            cache[this] = result
            return result
        }

        fun collectAccessorsTo(dst: IntOpenHashSet) {
            if (isFinal) {
                dst.add(FINAL_ACCESSOR_IDX)
            }

            forEachAccessor { accessor, accessorNode ->
                if (accessor != ANY_ACCESSOR_IDX) {
                    // note: always ignore any accessor.
                    //
                    // Deliberately asymmetric with the premise side: [AccessPath.getAllAccessors]
                    // DOES report `AnyAccessor`, and its consumers filter it out explicitly (see
                    // MethodSideEffectHandlerWithAnyAccessorRequestHandling.handleFactToFact).
                    // Keep both sides as they are. Here the set answers "which concrete accessors
                    // does this fact mention", and `[any]` names none of them. There it answers
                    // "which links does this premise have", and dropping `[any]` would make an
                    // `[any]`-only premise indistinguishable from a bare, unrefined one.
                    dst.add(accessor)
                }

                accessorNode.collectAccessorsTo(dst)
            }
        }

        private fun bulkMergeAddAccessors(
            accessors: List<IntObjectImmutablePair<AccessNode>>,
            entryAnyState: AnyUnrollState?,
            absorbing: Boolean = true,
        ): AccessNode {
            // THE GRAFT. `concat` rebuilds the receiver's spine through here, so this is the site
            // the design exists for: `arg0.[any].*` reads `a` for premise `arg0.a`, and the
            // remainder -- which still carries the `[any]` -- is re-installed under conclusion
            // `ret.a.*`, giving `ret.a.[any].*`. Same number of `[any]` edges, one more link, every
            // lap. The budget stops the operation that is free and never looks at this one.
            val (entries, absorbedState) = absorbBeyondAnyEntries(accessors, absorbing)

            // Unconditional and BEFORE the early return: the union is a side effect of the merge,
            // and an implementation that short-circuits past it loses the transition that makes a
            // program loop reach its fixed point.
            val mergedAnyId = manager.anyUnroll.union(manager.anyUnroll.union(anyId, entryAnyState), absorbedState)

            if (entries.isEmpty()) return this

            val groupedUniqueAccessors = Int2ObjectOpenHashMap<MutableList<AccessNode>>()
            entries.forEach { accessorWithNode ->
                val group = groupedUniqueAccessors.getOrCreate(accessorWithNode.leftInt(), ::mutableListOf)
                group.add(accessorWithNode.right())
            }

            val uniqueAccessors = mutableListOf<IntObjectImmutablePair<AccessNode>>()
            groupedUniqueAccessors.forEachIntEntry { accessor, nodes ->
                val mergedNodes = nodes.reduce { acc, node -> acc.mergeAdd(node) }
                uniqueAccessors.add(IntObjectImmutablePair(accessor, mergedNodes))
            }

            uniqueAccessors.sortBy { it.firstInt() }
            val addedAccessors = IntArray(uniqueAccessors.size) { uniqueAccessors[it].firstInt() }
            val addedNodes = Array(uniqueAccessors.size) { uniqueAccessors[it].second() }

            val mergedAccessors = mergeAccessors(
                addedAccessors, addedNodes, onOtherNode = { _, _ -> }
            ) { _, thisNode, otherNode ->
                thisNode.mergeAdd(otherNode)
            }

            if (mergedAccessors == null) return this

            return manager.create(
                isAbstract, isFinal, deepAccessorExclusion, mergedAccessors.first, mergedAccessors.second,
                anyStateIfPresent(mergedAccessors.first, mergedAnyId),
            )
        }

        /**
         * The list-to-list form of the absorbing prepend, for the one funnel that takes a list.
         *
         * Returns the rewritten entries and the union of every predecessor absorbed into, which the
         * caller must fold into the state of the resulting `[any]` slot -- the entry's own state
         * disappears with the edge otherwise.
         *
         * **The guard order is not stylistic.** `isCoveredByAny` delegates straight to the injected
         * strategy and the one installed for the whole prescan phase THROWS rather than returning
         * false -- and both callers run during prescan. Probing `node.anyId != null` first makes the
         * coverage query unreachable there, because with the manager disabled every `anyId` is null.
         * `normaliseUnderAny` carries a dedicated short-circuit for exactly the same reason.
         *
         * **On the depth-relative claim.** `DeepAccessorExclusion` is depth-relative and this rewrite
         * hoists, so in principle it owes the same report `absorbCoveredByAnyPrefix` makes. It does
         * not, because of where it runs: in `concat` the receiver is a freshly created node with
         * `deepAccessorExclusion = null` and the delta's flag is computed on `concatNode`, a disjoint
         * object filtered in the same frame; in `addParentFieldAccess` the receiver comes out of
         * `create`, which sets it null too. `graftAbsorbUnderClaim` is the falsifier -- it must stay
         * zero, and a non-zero reading means a receiver carrying a claim reached this rewrite and the
         * report is genuinely owed.
         */
        private fun absorbBeyondAnyEntries(
            accessors: List<IntObjectImmutablePair<AccessNode>>,
            absorbing: Boolean,
        ): Pair<List<IntObjectImmutablePair<AccessNode>>, AnyUnrollState?> {
            if (!absorbing || !manager.anyUnroll.enabled || accessors.isEmpty()) return accessors to null

            var rewritten: MutableList<IntObjectImmutablePair<AccessNode>>? = null
            var absorbedState: AnyUnrollState? = null

            for (i in accessors.indices) {
                val entry = accessors[i]
                val accessor = entry.leftInt()
                val node = entry.right()

                val pred = absorbTargetFor(accessor, node)
                if (pred == null) {
                    rewritten?.add(entry)
                    continue
                }

                if (rewritten == null) {
                    rewritten = ArrayList(accessors.size + 1)
                    for (j in 0 until i) rewritten.add(accessors[j])
                }

                if (AnyUnrollDiagnostics.enabled) {
                    AnyUnrollDiagnostics.absorptions.incrementAndGet()
                    AnyUnrollDiagnostics.graftAbsorbs.incrementAndGet()
                    if (deepAccessorExclusion != null) {
                        AnyUnrollDiagnostics.graftAbsorbUnderClaim.incrementAndGet()
                    }
                }

                // The SPLIT, in list form: the step is dropped only on the `[any]`-rooted branch and
                // kept on every concrete sibling, because dropping it across the whole entry would
                // rewrite `a.f.S` as `f.S` -- neither superset nor subset.
                val anyChild = node.getNodeByAccessor(ANY_ACCESSOR_IDX)!!
                val rest = node.clearChild(ANY_ACCESSOR_IDX)
                if (!rest.isEmpty) rewritten.add(IntObjectImmutablePair(accessor, rest))
                rewritten.add(IntObjectImmutablePair(ANY_ACCESSOR_IDX, anyChild))

                // The receiver is the ACCUMULATED side, so its representative is the one that
                // survives -- the same obligation every `mergeAdd` call site here carries.
                absorbedState = manager.anyUnroll.union(absorbedState, pred)
            }

            return (rewritten ?: accessors) to absorbedState
        }

        /**
         * The guard chain of the absorbing prepend, in the order the throwing query requires.
         *
         * @param count whether to record the outcome. The excluded caller runs this probe purely to
         *   measure what its exclusion saves, and counting there would put its non-events into the
         *   same buckets as the real ones.
         */
        /**
         * What the declined prepend WOULD have done, had the kind gate been open.
         *
         * The gate is the reason 99.7% of prepends write their step, which is a fact about the
         * gate and not yet a fact about the cost. Running the rest of the probe here separates
         * "the pattern was absorbable and the gate refused it" from "there was nothing to absorb":
         * a position with no incoming edge for this accessor, or one whose only incoming edge is a
         * self-loop, is not structure the gate is holding back.
         */
        private fun recordDeclinedPrepend(accessor: AccessorIdx, node: AccessNode, pos: AnyUnrollState) {
            val kind = manager.anyUnroll.kindOf(pos)
            when (kind) {
                AnyUnrollKind.ORIGIN -> AnyUnrollDiagnostics.cfDeclinedOrigin
                else -> AnyUnrollDiagnostics.cfDeclinedPaid
            }.incrementAndGet()
            val state = pos.find()
            val dag = manager.anyUnroll.dagOf(state)
            AnyUnrollDiagnostics.recordDeclineByState(
                state.id,
                (if (state.mintedByUnroll) "$kind/unroll" else "$kind/read") +
                    " dag#${dag?.id} total=${dag?.total} states=${dag?.states}"
            )

            val anyNode = node.getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return
            val name = with(manager) { accessor.accessor }.toSuffix()

            if (anyNode.getNodeByAccessor(accessor) != null) {
                AnyUnrollDiagnostics.cfGuardBlocked.incrementAndGet()
                AnyUnrollDiagnostics.sampleCounterfactual("guardBlocked $name") { anyNode.render() }
                return
            }
            if (!manager.isCoveredByAny(accessor)) {
                AnyUnrollDiagnostics.cfUncovered.incrementAndGet()
                AnyUnrollDiagnostics.sampleCounterfactual("uncovered $name") { anyNode.render() }
                return
            }

            val pred = manager.anyUnroll.absorbInto(pos, accessor, count = false)
            when {
                pred == null -> {
                    AnyUnrollDiagnostics.cfNoPredecessor.incrementAndGet()
                    AnyUnrollDiagnostics.sampleCounterfactual("noPredecessor $name") { anyNode.render() }
                }
                pred === pos.find() -> {
                    AnyUnrollDiagnostics.cfWouldStay.incrementAndGet()
                    AnyUnrollDiagnostics.sampleCounterfactual("wouldStay $name") { anyNode.render() }
                }
                else -> {
                    AnyUnrollDiagnostics.cfWouldMove.incrementAndGet()
                    AnyUnrollDiagnostics.sampleCounterfactual("wouldMove $name") { anyNode.render() }
                }
            }
        }

        private fun AccessNode.render(): String =
            "kind=" + manager.anyUnroll.kindOf(anyId) + " anySubtree=" + toString().replace('\n', ' ')

        private fun absorbTargetFor(
            accessor: AccessorIdx,
            node: AccessNode,
            count: Boolean = true,
        ): AnyUnrollState? {
            val pos = node.anyId ?: return null
            if (accessor == ANY_ACCESSOR_IDX) return null
            val counting = count && AnyUnrollDiagnostics.enabled

            if (manager.anyUnroll.writesAbove(pos)) {
                if (counting) {
                    AnyUnrollDiagnostics.prependWrittenPaid.incrementAndGet()
                    recordDeclinedPrepend(accessor, node, pos)
                }
                return null
            }
            // By the node invariant `anyId != null` iff there is an `[any]` edge, so this is non-null.
            val anyNode = node.getNodeByAccessor(ANY_ACCESSOR_IDX) ?: return null
            if (anyNode.getNodeByAccessor(accessor) != null) {
                if (counting) AnyUnrollDiagnostics.prependGuardBlocked.incrementAndGet()
                return null
            }
            if (!manager.isCoveredByAny(accessor)) {
                if (counting) AnyUnrollDiagnostics.prependUncovered.incrementAndGet()
                return null
            }

            val pred = manager.anyUnroll.absorbInto(pos, accessor)
            if (counting) {
                when {
                    pred == null -> AnyUnrollDiagnostics.prependWrittenCreditMismatch
                    pred === pos.find() -> AnyUnrollDiagnostics.absorbStay
                    else -> AnyUnrollDiagnostics.absorbExact
                }.incrementAndGet()
            }
            return pred
        }

        private data class AccessNodeMergePair(val left: AccessNode, val right: AccessNode) {
            private val hash = System.identityHashCode(left) * 31 + System.identityHashCode(right)

            override fun hashCode(): Int = hash

            override fun equals(other: Any?): Boolean {
                if (this === other) return true
                if (other !is AccessNodeMergePair) return false
                return left === other.left && right === other.right
            }
        }

        fun mergeAdd(other: AccessNode, foldToAny: Boolean = true): AccessNode =
            mergeNodeLoop(other, foldToAny, { it }) { a, b, results ->
                a.mergeAddStep(b, results)
            }

        private fun intersectDeepExclusion(other: AccessNode): DeepAccessorExclusion? = when {
            !this.isAbstract -> other.deepAccessorExclusion
            !other.isAbstract -> this.deepAccessorExclusion
            else -> DeepAccessorExclusion.intersect(this.deepAccessorExclusion, other.deepAccessorExclusion)
        }

        private fun mergeAddStep(
            other: AccessNode,
            results: Object2ObjectOpenHashMap<AccessNodeMergePair, AccessNode>
        ): AccessNode {
            // R3, and it MUST run before the unchanged-guard below. The guard returns the receiver
            // object, which is what the storage layer's `===` test keys on; an implementation that
            // tested the shape first and returned early would skip the union, the self-loop that a
            // program loop's fixed point rests on would never form, and the analysis would not
            // terminate. Preferring the receiver's representative is also what lets the guard fire on
            // the SAME round rather than one lap later.
            val mergedAnyId = manager.anyUnroll.union(this.anyId, other.anyId)

            val isAbstract = this.isAbstract || other.isAbstract
            val isFinal = this.isFinal || other.isFinal
            val deepExclusions = intersectDeepExclusion(other)

            val mergedAccessors = mergeAccessors(
                other.accessors, other.accessorNodes, onOtherNode = { _, _ -> }
            ) { _, thisNode, otherNode ->
                results.getComputedResult(AccessNodeMergePair(thisNode, otherNode))
            }
            if (
                isAbstract == this.isAbstract
                && isFinal == this.isFinal
                && deepExclusions == this.deepAccessorExclusion
                && mergedAccessors == null
            ) {
                return this
            }

            val accessors = mergedAccessors?.first ?: accessors
            val accessorNodes = mergedAccessors?.second ?: accessorNodes

            return manager.create(
                isAbstract, isFinal, deepExclusions, accessors, accessorNodes,
                anyStateIfPresent(accessors, mergedAnyId),
            )
        }

        fun mergeAddDelta(other: AccessNode, foldToAny: Boolean = true): Pair<AccessNode, AccessNode?> =
            mergeNodeLoop<Pair<AccessNode, AccessNode?>>(other, foldToAny, { it to null }) { a, b, results ->
                a.mergeAddDeltaStep(b, results)
            }

        private fun mergeAddDeltaStep(
            other: AccessNode,
            results: Object2ObjectOpenHashMap<AccessNodeMergePair, Pair<AccessNode, AccessNode?>>,
        ): Pair<AccessNode, AccessNode?> {
            // R3; see [mergeAddStep] for why this cannot move below the guard.
            val mergedAnyId = manager.anyUnroll.union(this.anyId, other.anyId)

            val isFinal = this.isFinal || other.isFinal
            val isFinalDelta = !this.isFinal && other.isFinal

            val isAbstract = this.isAbstract || other.isAbstract
            val deepExclusion = intersectDeepExclusion(other)

            val abstractionPointChanged = isAbstract != this.isAbstract || deepExclusion != this.deepAccessorExclusion
            val isAbstractDelta = abstractionPointChanged && isAbstract
            val deltaDeepExclusion = if (isAbstractDelta) deepExclusion else null

            val deltaAccessors = IntArrayList()
            val deltaAccessorNodes = arrayListOf<AccessNode>()

            val mergedAccessors = mergeAccessors(
                other.accessors, other.accessorNodes,
                onOtherNode = { field, node ->
                    deltaAccessors.add(field)
                    deltaAccessorNodes.add(node)
                }
            ) { field, thisNode, otherNode ->
                val (addedNode, addedNodeDelta) = results.getComputedResult(AccessNodeMergePair(thisNode, otherNode))

                if (addedNodeDelta != null) {
                    deltaAccessors.add(field)
                    deltaAccessorNodes.add(addedNodeDelta)
                }

                addedNode
            }

            if (
                !abstractionPointChanged
                && isFinal == this.isFinal
                && mergedAccessors == null
            ) {
                return this to null
            }

            // The delta is what PROPAGATES, so an id-less delta would strand the manager at the far
            // end of the propagation: it gets the same representative.
            val deltaAccessorsArray = deltaAccessors.toIntArray()
            val delta = manager.create(
                isAbstractDelta, isFinalDelta, deltaDeepExclusion,
                deltaAccessorsArray, deltaAccessorNodes.toTypedArray(),
                anyStateIfPresent(deltaAccessorsArray, mergedAnyId),
            ).takeIf { !it.isEmpty }

            val accessors = mergedAccessors?.first ?: accessors
            val accessorNodes = mergedAccessors?.second ?: accessorNodes

            return manager.create(
                isAbstract, isFinal, deepExclusion, accessors, accessorNodes,
                anyStateIfPresent(accessors, mergedAnyId),
            ) to delta
        }

        private inline fun <T: Any> mergeNodeLoop(
            other: AccessNode,
            foldToAny: Boolean,
            mergeSameNode: (AccessNode) -> T,
            mergeNodes: (AccessNode, AccessNode, cache: Object2ObjectOpenHashMap<AccessNodeMergePair, T>) -> T
        ): T {
            if (this === other) return mergeSameNode(this)

            val results = Object2ObjectOpenHashMap<AccessNodeMergePair, Any>()
            val stack = mutableListOf<AccessNodeMergePair>()

            val initial = AccessNodeMergePair(this, other)
            stack.add(initial)

            while (stack.isNotEmpty()) {
                val mergePair = stack.last()

                val (a, b) = mergePair
                if (a === b) {
                    results[mergePair] = mergeSameNode(a)
                    stack.removeLast()
                    continue
                }

                val currentResult = results.putIfAbsent(mergePair, NodeExpansionRequested)
                if (currentResult != null && currentResult !== NodeExpansionRequested) {
                    if (currentResult is AccessNodeMergePair) {
                        results[mergePair] = results[currentResult]
                    }
                    stack.removeLast()
                    continue
                }

                if (currentResult == null) {
                    if (foldToAny) {
                        trimAnyCoveredAndPushChildren(mergePair, stack, results)
                    }
                    else {
                        pushSharedChildPairs(a, b, stack)
                    }
                    continue
                }

                // currentResult === NodeExpansionRequested
                @Suppress("UNCHECKED_CAST")
                results[mergePair] = mergeNodes(a, b, results as Object2ObjectOpenHashMap<AccessNodeMergePair, T>)
                stack.removeLast()
            }

            @Suppress("UNCHECKED_CAST")
            return (results as Object2ObjectOpenHashMap<AccessNodeMergePair, T>).getComputedResult(initial)
        }

        /**
         * The single entry point for building an `[any]` suffix matcher -- see [anySuffixMatcher]
         * for why building it twice under a race is safe.
         */
        private fun AccessNode.suffixMatcher(): AccessTreeAnySuffixMatcher =
            anySuffixMatcher ?: AccessTreeAnySuffixMatcher(this).also { anySuffixMatcher = it }

        private fun trimAnyCoveredAndPushChildren(
            mergePair: AccessNodeMergePair,
            stack: MutableList<AccessNodeMergePair>,
            results: Object2ObjectOpenHashMap<AccessNodeMergePair, Any>,
        ) {
            val (a, b) = mergePair

            // R3, here rather than only in [mergeAddStep], because when the trim below substitutes a
            // pair, [mergeNodeLoop] resolves the original through `results[currentResult]` and never
            // calls the merge step for it at all -- so the step's own union would be skipped. Worse,
            // the trim is exactly what DELETES one side's `[any]` edge, so the state it would have
            // carried is gone by the time anything else could union it. This runs on every merge
            // pair with `foldToAny`, which is the default and includes `getChild`'s own arm.
            manager.anyUnroll.union(a.anyId, b.anyId)

            if (a.accessors == null || b.accessors == null)
                return

            val aAccessorsUntrimmed = a.accessors
            val aNodesUntrimmed = a.accessorNodes!!

            val aAnyIdx = aAccessorsUntrimmed.indexOf(ANY_ACCESSOR_IDX)
            val bTrimmed =
                if (aAnyIdx >= 0)
                    aNodesUntrimmed[aAnyIdx].suffixMatcher().getNonMatchingNode(b)
                else b

            val bAccessorsUntrimmed = bTrimmed.accessors
            val bNodesUntrimmed = bTrimmed.accessorNodes

            val bAnyIdx = bAccessorsUntrimmed?.indexOf(ANY_ACCESSOR_IDX) ?: -1
            val aTrimmed =
                if (bAnyIdx >= 0)
                    bNodesUntrimmed!![bAnyIdx].suffixMatcher().getNonMatchingNode(a)
                else a

            if (aTrimmed !== a || bTrimmed !== b) {
                val trimmedPair = AccessNodeMergePair(aTrimmed, bTrimmed)
                results[mergePair] = trimmedPair
                stack.add(trimmedPair)
                results[trimmedPair] = NodeExpansionRequested
                pushSharedChildPairs(aTrimmed, bTrimmed, stack)
            }
            else {
                pushSharedChildPairs(a, b, stack)
            }
        }

        private fun pushSharedChildPairs(
            a: AccessNode,
            b: AccessNode,
            stack: MutableList<AccessNodeMergePair>,
        ) {
            val aAccessors = a.accessors ?: return
            val bAccessors = b.accessors ?: return
            val aNodes = a.accessorNodes!!
            val bNodes = b.accessorNodes!!

            var ai = 0
            var bi = 0
            while (ai < aAccessors.size && bi < bAccessors.size) {
                val cmp = aAccessors[ai].compareTo(bAccessors[bi])
                when {
                    cmp < 0 -> ai++
                    cmp > 0 -> bi++
                    else -> {
                        stack.add(AccessNodeMergePair(aNodes[ai], bNodes[bi]))
                        ai++
                        bi++
                    }
                }
            }
        }

        fun filterAccessNode(filter: FactTypeChecker.FactApFilter): AccessNode? = with(manager) {
            var result = transformAccessors { accessor, accessNode ->
                when (val status = filter.check(accessor.accessor)) {
                    FactTypeChecker.FilterResult.Accept -> accessNode
                    FactTypeChecker.FilterResult.Reject -> null
                    is FactTypeChecker.FilterResult.FilterNext -> accessNode.filterAccessNode(status.filter)
                }
            }

            if (result.isFinal) {
                result = when (filter.check(FinalAccessor)) {
                    FactTypeChecker.FilterResult.Accept -> result
                    is FactTypeChecker.FilterResult.FilterNext -> result
                    FactTypeChecker.FilterResult.Reject -> result.clearChild(FINAL_ACCESSOR_IDX)
                }
            }

            return result.takeIf { !it.isEmpty }
        }

        fun filterAccessNode(
            checker: FactTypeChecker.FactCompatibilityFilter,
        ): AccessNode? {
            val interned = internNodes(AccessTreeInterner(), IdentityHashMap())
            return interned.filterAccessNodeCached(checker)
        }

        fun filterAccessNodeCached(
            checker: FactTypeChecker.FactCompatibilityFilter
        ): AccessNode? {
            val results = IdentityHashMap<AccessNode, AccessNode?>()
            val expanded = IdentityHashMap<AccessNode, Unit>()
            val stack = mutableListOf<AccessNode>()
            stack.add(this)

            while (stack.isNotEmpty()) {
                val node = stack.last()

                if (results.containsKey(node)) {
                    stack.removeLast()
                    continue
                }

                if (expanded.containsKey(node)) {
                    results[node] = node.filterChildren(checker, results)
                    stack.removeLast()
                    continue
                }

                expanded[node] = Unit
                node.accessorNodes?.forEach { stack.add(it) }
            }

            return results[this]
        }

        private fun filterChildren(
            checker: FactTypeChecker.FactCompatibilityFilter,
            childResults: IdentityHashMap<AccessNode, AccessNode?>,
        ): AccessNode? = transformAccessorsNonEmpty { accessor, child ->
            val checkedNode = childResults[child] ?: return@transformAccessorsNonEmpty null

            if (!checkedNode.isAbstract) {
                return@transformAccessorsNonEmpty checkedNode
            }

            val checkResult = with(manager) { checker.check(accessor.accessor) }
            when (checkResult) {
                is FactTypeChecker.CompatibilityFilterResult.Compatible ->
                    checkedNode

                is FactTypeChecker.CompatibilityFilterResult.NotCompatible ->
                    checkedNode.removeAbstraction().takeIf { !it.isEmpty }
            }
        }

        fun concatToLeafAbstractNodes(
            typeChecker: FactTypeChecker,
            other: AccessNode
        ): AccessNode? {
            val filteredOther = FilteredNode.create(manager, other)

            val graftCounter = if (ApOpDiagnostics.enabled) {
                ApOpDiagnostics.graftPointCounter.get().also { it.value = 0 }
            } else null

            val result = concatToLeafAbstractNodes(
                typeChecker, filteredOther, IntArrayList(), SUBSEQUENT_ARRAY_ELEMENTS_LIMIT,
                parentEdgeIsAny = false,
            )

            if (ApOpDiagnostics.enabled) {
                val out0 = result?.size ?: 0L
                ApOpDiagnostics.recordConcatShape(graftCounter?.value ?: 0, maxOf(0L, out0 - this.size))

                if (other.containsAnyInThisOrDeepNodes) {
                    // The other half of the round trip: the conclusion supplies a concrete prefix and
                    // the `[any]`-carrying remainder is hung below it, so the fact comes out longer
                    // AND still carrying an `[any]`.
                    ApOpDiagnostics.concatAnyDeltaCalls.incrementAndGet()
                    ApOpDiagnostics.concatAnyDeltaDepthGain.addAndGet(
                        maxOf(0, (result?.maxDepth ?: 0) - this.maxDepth).toLong()
                    )
                    if (result?.containsAnyInThisOrDeepNodes == true) {
                        ApOpDiagnostics.concatAnyDeltaResultKeepsAny.incrementAndGet()
                    }
                }

                if (ApOpDiagnostics.concatShouldSample()) {
                    ApOpDiagnostics.concatSamples.incrementAndGet()
                    ApOpDiagnostics.concatSampleRecvSize.addAndGet(this.size)
                    ApOpDiagnostics.concatSampleRecvDistinct.addAndGet(this.countNodes().toLong())
                    ApOpDiagnostics.concatSampleRecvAbstract.addAndGet(countAbstractNodes().toLong())
                    ApOpDiagnostics.concatSampleDeltaSize.addAndGet(other.size)
                    ApOpDiagnostics.concatSampleDeltaDistinct.addAndGet(other.countNodes().toLong())
                    ApOpDiagnostics.concatSampleResultSize.addAndGet(out0)
                    ApOpDiagnostics.concatSampleResultDistinct.addAndGet(result?.countNodes()?.toLong() ?: 0L)
                }
            }

            if (ApOpDiagnostics.enabled) {
                val out = result?.size ?: 0L
                ApOpDiagnostics.concatCalls.incrementAndGet()
                ApOpDiagnostics.concatReceiverNodes.addAndGet(this.size)
                ApOpDiagnostics.concatDeltaNodes.addAndGet(other.size)
                ApOpDiagnostics.concatResultNodes.addAndGet(out)
                ApOpDiagnostics.recordConcatSite(
                    receiver = this.size,
                    result = out,
                    graftPoints = graftCounter?.value ?: 0,
                    deltaCarriesAny = other.containsAnyInThisOrDeepNodes,
                ) {
                    "receiver(size=" + this.size + ") + delta(size=" + other.size + ") -> " + out +
                        "; delta=" + other.toString().replace('\n', ' ')
                }
                if (out > this.size) {
                    ApOpDiagnostics.concatGrew.incrementAndGet()
                    ApOpDiagnostics.concatGrowth.addAndGet(out - this.size)
                    ApOpDiagnostics.example("C-concat", out - this.size) {
                        "graft delta(size=" + other.size + ") onto receiver(size=" + this.size +
                            ") -> " + out + "; delta=" + other.toString().replace('\n', ' ')
                    }
                }
            }

            return result
        }

        fun internNodes(
            interner: AccessTreeInterner,
            cache: IdentityHashMap<AccessNode, AccessNode>,
        ): AccessNode = internNodesWithCache(interner, cache)

        private fun internNodesWithCache(
            interner: AccessTreeInterner,
            cache: IdentityHashMap<AccessNode, AccessNode>,
        ): AccessNode {
            if (interned) return this

            val stack = mutableListOf<AccessNode>()
            val expanded = IdentityHashMap<AccessNode, Unit>()
            stack.add(this)

            while (stack.isNotEmpty()) {
                manager.cancellation.checkpoint()

                val node = stack.last()

                if (cache.containsKey(node)) {
                    stack.removeLast()
                    continue
                }

                if (expanded.containsKey(node)) {
                    val withInternedChildren = node.transformAccessors { _, child -> cache[child] }
                    cache[node] = interner.intern(withInternedChildren.markInterned())
                    stack.removeLast()
                    continue
                }

                if (node.interned) {
                    cache[node] = node
                    stack.removeLast()
                    continue
                }

                expanded[node] = Unit
                node.forEachAccessor { _, child ->
                    if (!cache.containsKey(child)) {
                        stack.add(child)
                    }
                }
            }

            return cache[this] ?: error("Impossible")
        }

        private fun markInterned() = AccessNode(
            manager,
            interned = true,
            isAbstract = isAbstract,
            isFinal = isFinal,
            deepAccessorExclusion = deepAccessorExclusion,
            accessors = accessors,
            accessorNodes = accessorNodes,
            anyIdRaw = anyId,
        )

        private class FilteredNode(
            val manager: TreeApManager,
            val node: AccessNode,
            val allNodeAccessors: IdentityHashMap<AccessNode, IntOpenHashSet>,
            val cache: IdentityHashMap<AccessNode, Int2ObjectOpenHashMap<Optional<Pair<AccessNode, List<IntObjectImmutablePair<AccessNode>>>>>>,
            val typeFilterCache: IdentityHashMap<AccessNode, MutableMap<FactTypeChecker.FactApFilter, Optional<AccessNode>>>,
            val absorbCache: IdentityHashMap<AccessNode, AccessNode>,
        ) {
            private fun updateNode(node: AccessNode) =
                FilteredNode(manager, node, allNodeAccessors, cache, typeFilterCache, absorbCache)

            /**
             * [AccessNode.absorbCoveredByAnyPrefix] lifted to the filtered wrapper: the absorbed
             * sibling, plus whether any step was consumed (C2 needs the flag).
             *
             * The absorbed node is a fresh node, so it has no [allNodeAccessors] entry and
             * [limitFieldAccess] would fall back to the full walk -- safe, since a MISSING entry
             * means "unknown, do the work", but it forfeits exactly the O(1) that C0 is after.
             * A WRONG entry would instead be a correctness bug, so the entry is computed EXACTLY,
             * from the absorbed node itself. The walk is memoized in the same map, so the interned
             * subtrees hanging below the absorbed spine are already present and cost nothing.
             */
            fun absorbCoveredByAnyPrefix(): Pair<FilteredNode, Boolean> {
                absorbCache[node]?.let { cached ->
                    return if (cached === node) this to false else updateNode(cached) to true
                }

                val (absorbedNode, absorbedAnyStep) = node.absorbCoveredByAnyPrefix()
                absorbCache[node] = absorbedNode

                if (!absorbedAnyStep) return this to false

                collectAllAccessors(absorbedNode, allNodeAccessors)

                return updateNode(absorbedNode) to true
            }

            fun filterTypes(typeChecker: FactTypeChecker, path: IntArrayList): FilteredNode? {
                val accessorPath = with(manager) { path.map { it.accessor } }
                val filter = typeChecker.accessPathFilter(accessorPath)

                val nodeCache = typeFilterCache.getOrPut(node, ::hashMapOf)
                val filterCache = nodeCache[filter]
                if (filterCache != null) {
                    val filteredNode = filterCache.getOrNull()
                        ?: return null

                    return updateNode(filteredNode)
                }

                val filteredNode = node.filterAccessNode(filter)

                if (filteredNode == null) {
                    nodeCache[filter] = Optional.empty()
                    return null
                }

                nodeCache[filter] = Optional.of(filteredNode)

                return updateNode(filteredNode)
            }

            fun limitFieldAccess(
                accessor: AccessorIdx,
                filteredNodes: MutableList<IntObjectImmutablePair<AccessNode>>
            ): FilteredNode? {
                val nodeAccessors = allNodeAccessors[node]
                if (nodeAccessors != null && !nodeAccessors.contains(accessor)) return this

                val nodeCache = cache.getOrPut(node, ::Int2ObjectOpenHashMap)
                val accessorResult = nodeCache.get(accessor)
                if (accessorResult != null) {
                    val unpackedResult = accessorResult.getOrNull()
                        ?: return null

                    filteredNodes += unpackedResult.second
                    return updateNode(unpackedResult.first)
                }

                val extractedNodes = mutableListOf<IntObjectImmutablePair<AccessNode>>()
                val filteredNode = node.limitFieldAccess(accessor, extractedNodes)
                if (filteredNode == null) {
                    nodeCache[accessor] = Optional.empty()
                    return null
                }

                if (nodeAccessors != null) {
                    val newAccessors = nodeAccessors.clone()
                    newAccessors.remove(accessor)
                    allNodeAccessors[filteredNode] = newAccessors
                }

                nodeCache[accessor] = Optional.of(filteredNode to extractedNodes)

                filteredNodes += extractedNodes
                return updateNode(filteredNode)
            }

            companion object {
                fun create(manager: TreeApManager, node: AccessNode): FilteredNode {
                    val internedNode = node.internNodes(AccessTreeInterner(), IdentityHashMap())
                    val allAccessors = IdentityHashMap<AccessNode, IntOpenHashSet>()
                    collectAllAccessors(internedNode, allAccessors)
                    return FilteredNode(
                        manager, internedNode, allAccessors,
                        IdentityHashMap(), IdentityHashMap(), IdentityHashMap()
                    )
                }

                private fun collectAllAccessors(
                    node: AccessNode,
                    cache: IdentityHashMap<AccessNode, IntOpenHashSet>
                ): IntOpenHashSet {
                    cache[node]?.let { return it }

                    val allAccessors = IntOpenHashSet()
                    node.forEachAccessor { accessor, child ->
                        allAccessors.add(accessor)
                        allAccessors += collectAllAccessors(child, cache)
                    }

                    cache[node] = allAccessors
                    return allAccessors
                }
            }
        }

        /**
         * [parentEdgeIsAny] is C4 of the concat absorption: ONLY an abstract node whose IMMEDIATE
         * parent edge is `[any]` may absorb the covered prefix of the delta grafted onto it.
         * Consuming into a path such as `[any].f.*` would be unsound -- `[any].f.x.![m]` and
         * `[any].f.![m]` are disjoint path sets -- so the flag is set by the descent for exactly one
         * level and is never inherited. It is deliberately kept apart from C2's absorbed-depth
         * bookkeeping, which is derived locally at the graft point from what absorption actually
         * consumed there and likewise never travels: a delta handed further down the recursion is
         * always the UNABSORBED one, so no deeper frame's depths have been disturbed.
         */
        private fun concatToLeafAbstractNodes(
            typeChecker: FactTypeChecker,
            other: FilteredNode?,
            path: IntArrayList,
            subsequentArrayElementLimit: Int,
            parentEdgeIsAny: Boolean,
        ): AccessNode? {
            manager.cancellation.checkpoint()

            if (ApOpDiagnostics.enabled && isAbstract && other != null) {
                // One increment per abstract node the delta is actually offered to. `k` in
                // `|result| ~ |receiver| + k * |delta|`, and the only number that separates
                // "the graft multiplies" from "the graft relocates the caller's remainder once".
                ApOpDiagnostics.graftPointCounter.get().value++

                // ... and whether the filter about to run here can reject anything: see I-filter.
                ApOpDiagnostics.recordGraftFilterShape(
                    pathEmpty = path.size == 0,
                    pathEndsAny = path.size > 0 && path.getInt(path.size - 1) == ANY_ACCESSOR_IDX,
                    deltaNodes = other.node.size,
                )
            }

            val concatNode = if (isAbstract && other != null) {
                // C0: filterTypes stays first and at full precision -- it reads the delta's real
                // shape -- and absorption slots in ahead of the two limiters. Past it the residual's
                // head is, by construction, the first accessor `[any]` does NOT cover, so
                // limitElementAccess finds no leading element chain and limitFieldAccess (in the
                // descent below) finds no occurrence of the field to strip: both degenerate to
                // no-ops and do real work only when an uncovered accessor is actually present.
                // This is one of the hottest paths in the engine -- concatToLeafAbstractNodes
                // grafts at EVERY abstract node of the conclusion.
                val typeFiltered = other.filterTypes(typeChecker, path)

                val (absorbed, absorbedAnyStep) =
                    if (parentEdgeIsAny && typeFiltered != null) {
                        typeFiltered.absorbCoveredByAnyPrefix()
                    } else {
                        typeFiltered to false
                    }

                absorbed?.node?.limitElementAccess(limit = subsequentArrayElementLimit)
                    ?.filterDeepExclusion(deepAccessorExclusion, absorbedAnyStep)
            } else null

            val nestedAccessors = mutableListOf<IntObjectImmutablePair<AccessNode>>()

            forEachAccessor { accessor, node ->
                val filteredOther = if (accessor.isFieldAccessor()) {
                    other?.limitFieldAccess(accessor, nestedAccessors)
                } else {
                    other
                }

                val newSubsequentArrayLimit = if (accessor == ELEMENT_ACCESSOR_IDX) {
                    subsequentArrayElementLimit - 1
                } else {
                    SUBSEQUENT_ARRAY_ELEMENTS_LIMIT
                }

                path.add(accessor)
                val concatenatedNode = node.concatToLeafAbstractNodes(
                    typeChecker, filteredOther, path, newSubsequentArrayLimit,
                    parentEdgeIsAny = accessor == ANY_ACCESSOR_IDX,
                )
                path.removeLast()

                if (concatenatedNode != null) {
                    nestedAccessors.add(IntObjectImmutablePair(accessor, concatenatedNode))
                }
            }

            val resultNode = manager.create(isAbstract = false, isFinal, deepAccessorExclusion = null, accessors = null, accessorNodes = null, anyState = null)
                // `this.anyId` is the state of the receiver's own `[any]` edge, which the child loop
                // above re-adds as a nestedAccessors entry: concat rebuilds the spine, so the edge
                // is RE-INSTALLED with the grafted subtree already underneath it and one
                // normalisation sees the whole thing. That is what discharges the graft case without
                // threading a governing state down the recursion.
                .bulkMergeAddAccessors(nestedAccessors, anyId)

            val concatenatedNode = concatNode?.let { resultNode.mergeAdd(it) } ?: resultNode

            return concatenatedNode.takeIf { !it.isEmpty }
        }

        fun filterStartsWith(accessPath: AccessPath.AccessNode?): AccessNode? {
            if (ApOpDiagnostics.enabled) {
                ApOpDiagnostics.fswCalls.incrementAndGet()
                ApOpDiagnostics.fswInNodes.addAndGet(this.size)
            }
            val fswResult = filterStartsWithImpl(accessPath)
            if (ApOpDiagnostics.enabled) {
                val out = fswResult?.size ?: 0L
                ApOpDiagnostics.fswOutNodes.addAndGet(out)
                if (out > this.size) {
                    ApOpDiagnostics.fswGrew.incrementAndGet()
                    ApOpDiagnostics.fswGrowth.addAndGet(out - this.size)
                    ApOpDiagnostics.example("D-filterStartsWith", out - this.size) {
                        "match premise(len=" + (accessPath?.size ?: 0) + ") against fact(size=" +
                            this.size + ") -> " + out
                    }
                }
            }
            return fswResult
        }

        private fun filterStartsWithImpl(accessPath: AccessPath.AccessNode?): AccessNode? {
            if (accessPath == null) return this

            // Soundness-critical prefilter, not a cost gate: the walk below descends with getChild,
            // which SYNTHESISES children through an `[any]` edge to arbitrary depth, so maxDepth
            // under-approximates the reachable depth as soon as an `[any]` is in reach. Skipping a
            // match here is a lost flow, so the prefilter must not fire in that case.
            if (!containsAnyInThisOrDeepNodes && maxDepth < accessPath.size) {
                return null
            }

            val parentAccessors = IntArrayList()
            // The walk consumes an `[any]` edge at every step that crosses one, and the fold below
            // re-creates those edges RAW. Minting there would refill the budget on every
            // subscription match -- this is the single largest read channel in the engine -- and
            // dropping the state would strand every manager at the first storage hop. So the state
            // consumed at each step travels alongside the accessor.
            val parentAnyStates = mutableListOf<AnyUnrollState?>()

            var filteredTreeNode = this
            var currentApNode: AccessPath.AccessNode = accessPath

            while (true) {
                val accessor = currentApNode.accessor
                val consumedAnyState = filteredTreeNode.anyId

                filteredTreeNode = when (accessor) {
                    FINAL_ACCESSOR_IDX -> {
                        if (!filteredTreeNode.isFinal) return null

                        manager.finalNode
                    }

                    else -> {
                        filteredTreeNode.getChildRecording(accessor)
                            ?.also {
                                parentAccessors.add(accessor)
                                parentAnyStates.add(consumedAnyState)
                            }
                            ?: return null
                    }
                }

                currentApNode = currentApNode.next ?: break

                // Same soundness-critical prefilter as above, applied to the node reached so far:
                // getChild can keep synthesising below an `[any]`, so maxDepth is only an upper
                // bound on the reachable depth when no `[any]` is in reach from here.
                if (!filteredTreeNode.containsAnyInThisOrDeepNodes && filteredTreeNode.maxDepth < currentApNode.size) {
                    return null
                }
            }

            // The shadow telescope: how far the backward run of `a_k ... a_1` gets before it
            // dead-ends. A stall with links still above it is the growth mode a greedy pick pays
            // for -- a path existed and was not found, so the fact keeps a link it should have shed,
            // on every lap. Diagnostics only; it changes nothing below.
            if (AnyUnrollDiagnostics.enabled && manager.anyUnroll.enabled) {
                var probe = filteredTreeNode.anyId
                var stepped = 0
                for (i in parentAccessors.size - 1 downTo 0) {
                    val next = probe?.let { manager.anyUnroll.absorbInto(it, parentAccessors.getInt(i)) }
                    if (next == null) {
                        if (i > 0) {
                            AnyUnrollDiagnostics.telescopeStalls.incrementAndGet()
                            // The only population a subset construction could rescue: a fold that
                            // GOT somewhere and then dead-ended. One that stalls immediately was
                            // standing on a single state, where no set of positions exists yet.
                            if (stepped > 0) AnyUnrollDiagnostics.telescopeStallsAfterStep.incrementAndGet()
                        }
                        break
                    }
                    AnyUnrollDiagnostics.telescopeSteps.incrementAndGet()
                    stepped++
                    probe = next
                }
            }

            var result = filteredTreeNode
            for (i in parentAccessors.size - 1 downTo 0) {
                // This design in miniature, hand-wired. The descent above used `getChildRecording`,
                // so every accessor folded back here is an incoming edge of the state the fact
                // carries BY CONSTRUCTION -- the backward query cannot miss, and the rule absorbs
                // exactly the set the spent pot used to drop. The threaded state is the predecessor,
                // in hand three lines away, and the shipped absorb installed the SUCCESSOR instead.
                result = create(parentAccessors.getInt(i), result, parentAnyStates[i])
            }
            return result
        }

        private inline fun mergeAccessors(
            otherFields: IntArray?,
            otherNodesE: Array<AccessNode>?,
            onOtherNode: (AccessorIdx, AccessNode) -> Unit,
            merge: (AccessorIdx, AccessNode, AccessNode) -> AccessNode,
        ): Pair<IntArray, Array<AccessNode>>? {
            if (otherFields == null) return null
            val otherNodesBeforeAny = otherNodesE!!

            if (accessors == null) {
                for (i in otherFields.indices) {
                    onOtherNode(otherFields[i], otherNodesBeforeAny[i])
                }

                return otherFields to otherNodesBeforeAny
            }

            return mergeAccessorsRaw(accessors, accessorNodes!!, otherFields, otherNodesE, onOtherNode, merge)
        }

        private inline fun mergeAccessorsRaw(
            thisAccessors: IntArray,
            thisNodes: Array<AccessNode>,
            otherAccessors: IntArray,
            otherNodes: Array<AccessNode>,
            onOtherNode: (AccessorIdx, AccessNode) -> Unit,
            merge: (AccessorIdx, AccessNode, AccessNode) -> AccessNode,
        ): Pair<IntArray, Array<AccessNode>>? {
            var modified = false
            var accessorsModified = false

            var writeIdx = 0
            var thisIdx = 0
            var otherIdx = 0

            val mergedAccessors = IntArray(thisAccessors.size + otherAccessors.size)
            val mergedNodes = arrayOfNulls<AccessNode>(thisAccessors.size + otherAccessors.size)

            while (true) {
                val thisAccessor = thisAccessors.getOrElse(thisIdx) { -1 }
                val otherAccessor = otherAccessors.getOrElse(otherIdx) { -1 }

                if (thisAccessor == -1 && otherAccessor == -1) break

                val accessorsCmp = when {
                    otherAccessor == -1 -> -1 // thisField != null
                    thisAccessor == -1 -> 1 // otherField != null
                    else -> thisAccessor.compareTo(otherAccessor)
                }

                if (accessorsCmp < 0) {
                    mergedAccessors[writeIdx] = thisAccessor
                    mergedNodes[writeIdx] = thisNodes[thisIdx]
                    thisIdx++
                    writeIdx++
                } else if (accessorsCmp > 0) {
                    val otherNode = otherNodes[otherIdx]
                    onOtherNode(otherAccessor, otherNode)

                    modified = true
                    accessorsModified = true

                    mergedAccessors[writeIdx] = otherAccessor
                    mergedNodes[writeIdx] = otherNode
                    otherIdx++
                    writeIdx++
                } else {
                    val thisNode = thisNodes[thisIdx]
                    val otherNode = otherNodes[otherIdx]

                    val mergedNode = merge(thisAccessor, thisNode, otherNode)
                    if (mergedNode === thisNode) {
                        mergedAccessors[writeIdx] = thisAccessor
                        mergedNodes[writeIdx] = thisNode
                    } else {
                        modified = true
                        mergedAccessors[writeIdx] = thisAccessor
                        mergedNodes[writeIdx] = mergedNode
                    }

                    thisIdx++
                    otherIdx++
                    writeIdx++
                }
            }

            return trimModifiedAccessors(modified, accessorsModified, writeIdx, thisAccessors, mergedAccessors, mergedNodes)
        }

        private fun transformAccessorsNonEmpty(
            transformer: (AccessorIdx, AccessNode) -> AccessNode?
        ): AccessNode? = transformAccessors(transformer).takeIf { !it.isEmpty }

        private fun transformAccessors(
            transformer: (AccessorIdx, AccessNode) -> AccessNode?
        ): AccessNode {
            val newAccessors = transformAccessors(accessors, accessorNodes, transformer) ?: return this
            return recreate(isAbstract, isFinal, deepAccessorExclusion, newAccessors.first, newAccessors.second)
        }

        private fun limitFieldAccess(
            newRootField: AccessorIdx,
            filteredNodes: MutableList<IntObjectImmutablePair<AccessNode>>,
        ): AccessNode? {
            val cache = IdentityHashMap<AccessNode, AccessNode>()
            return limitFieldAccessCached(newRootField, filteredNodes, cache)
        }

        private fun limitFieldAccessCached(
            newRootField: AccessorIdx,
            filteredNodes: MutableList<IntObjectImmutablePair<AccessNode>>,
            cache: IdentityHashMap<AccessNode, AccessNode>,
        ): AccessNode? {
            cache[this]?.let { return it }

            manager.cancellation.checkpoint()

            val result = transformAccessorsNonEmpty { accessor, node ->
                if (accessor == newRootField) {
                    filteredNodes += IntObjectImmutablePair(accessor, node)
                    null
                } else {
                    node.limitFieldAccessCached(newRootField, filteredNodes, cache)
                }
            }

            cache[this] = result
            return result
        }

        fun removeAllAccessorChains(
            accessors: IntOpenHashSet,
            chainLengthToRemove: Int,
            cache: IdentityHashMap<AccessNode, AccessNode>,
            cancellation: Cancellation,
        ): AccessNode {
            cache[this]?.let { return it }

            cancellation.checkpoint()

            val removedNodes = mutableListOf<AccessNode>()
            val node = removeAllAccessorChains(accessors, removedNodes, chainLengthToRemove, 0, cache, cancellation)
            val mergedRemovedNode = removedNodes.reduceOrNull { acc, node -> acc.mergeAdd(node) }

            val result = if (mergedRemovedNode == null) {
                node ?: error("Impossible: No nodes removed")
            } else {
                node?.mergeAdd(mergedRemovedNode) ?: mergedRemovedNode
            }

            cache[this] = result
            return result
        }

        private fun removeAllAccessorChains(
            accessors: IntOpenHashSet,
            removedNodes: MutableList<AccessNode>,
            chainLengthToRemove: Int,
            currentChainLength: Int,
            cache: IdentityHashMap<AccessNode, AccessNode>,
            cancellation: Cancellation,
        ): AccessNode? {
            if (currentChainLength == chainLengthToRemove) {
                val node = removeAllAccessorChains(accessors, chainLengthToRemove, cache, cancellation)
                removedNodes += node
                return null
            }

            return transformAccessorsNonEmpty { accessor, node ->
                val transformed = node.removeAllAccessorChains(accessors, chainLengthToRemove, cache, cancellation)
                if (accessor !in accessors) return@transformAccessorsNonEmpty transformed

                // `[any]` is an ordinary vertex of the accessor graph, so an SCC may contain it and
                // this edge may be the one being deleted. The subtree is hoisted and keeps its own
                // states, but THIS node's state would simply vanish with the edge, and the origin
                // would then be free to spend a second full pot elsewhere.
                if (accessor == ANY_ACCESSOR_IDX) {
                    manager.anyUnroll.union(anyId, transformed.anyId)
                }

                transformed.removeAllAccessorChains(accessors, removedNodes, chainLengthToRemove, currentChainLength + 1, cache, cancellation)
            }
        }

        private fun removeSingleAccessor(accessor: AccessorIdx): AccessNode {
            val newAccessors = removeSingleAccessor(accessor, accessors, accessorNodes) ?: return this
            return recreate(isAbstract, isFinal, deepAccessorExclusion, newAccessors.first, newAccessors.second)
        }

        internal class Serializer(
            val manager: TreeApManager,
            private val context: SummarySerializationContext
        ) {
            private val deepExclusionsSerializer = with(manager) {
                DeepExclusionsSerializer(context, { it.idx }, { it.accessor })
            }

            fun DataOutputStream.writeAccessNode(node: AccessNode) {
                // A WIRE-FORMAT mask, unrelated to and deliberately not derived from
                // AccessNode.flags: it carries only the three serialised bits, in its own layout,
                // and must stay stable across changes to the in-memory packing.
                var mask = 0
                if (node.isFinal) {
                    mask += 1
                }
                if (node.isAbstract) {
                    mask += 2
                }
                if (node.deepAccessorExclusion != null) {
                    mask += 4
                }
                write(mask)

                node.deepAccessorExclusion?.let {
                    with(deepExclusionsSerializer) {
                        writeAnyFieldAccessorExclusions(it)
                    }
                }

                writeInt(node.accessors?.size ?: 0)
                if (node.accessors != null) {
                    node.accessors.forEach {
                        val accessor = with(manager) { it.accessor }
                        writeLong(context.getIdByAccessor(accessor))
                    }
                    node.accessorNodes!!.forEach { child ->
                        writeAccessNode(child)
                    }
                }
            }

            /**
             * A deserialised `[any]` arrives managerless and takes a fresh origin, i.e. a full
             * budget. That is sound -- more budget only means less coarsening -- and bounded at one
             * refill per cached summary, but it does mean a warm cache and a cold cache can produce
             * different precision.
             *
             * ONE state per deserialised TREE, threaded down the read, not one per `[any]` edge: the
             * read applies no invariant re-normalisation of its own, so a tree whose wire form
             * carried nested `[any]`s on one branch comes back with them intact, and minting per
             * edge would violate the branch invariant on the first such tree. It also matches what
             * the mint MEANS here: one cached summary, one origin.
             */
            fun DataInputStream.readAccessNode(): AccessNode =
                readAccessNode(arrayOfNulls(1))

            private fun DataInputStream.readAccessNode(treeAnyState: Array<AnyUnrollState?>): AccessNode {
                val mask = read()
                val isFinal = mask.and(1) > 0
                val isAbstract = mask.and(2) > 0

                val anyFieldAccessorExclusions = if (mask.and(4) > 0) {
                    with(deepExclusionsSerializer) {
                        readAnyFieldAccessorExclusions()
                    }
                } else {
                    null
                }

                val accessorsSize = readInt()
                if (accessorsSize == 0) {
                    return manager.create(
                        isAbstract, isFinal, anyFieldAccessorExclusions,
                        accessors = null, accessorNodes = null, anyState = null,
                    )
                }

                val deserializedAccessors = Array(accessorsSize) {
                    context.getAccessorById(readLong())
                }

                val deserializedAccessNodes = Array(accessorsSize) {
                    readAccessNode(treeAnyState)
                }

                val accessorNodes = hashMapOf<Accessor, AccessNode>()
                deserializedAccessNodes.forEachIndexed { index, node ->
                    val accessor = deserializedAccessors[index]
                    accessorNodes[accessor] = node
                }

                val accessorIndices = IntArray(accessorsSize) {
                    with(manager) { deserializedAccessors[it].idx }
                }

                val accessors = accessorIndices.sortedArray()
                val accessNodes = Array(accessorsSize) { dstIdx ->
                    val dstAccessor = with(manager) { accessors[dstIdx].accessor }
                    accessorNodes[dstAccessor] ?: error("Accessor mismatch: $dstAccessor")
                }

                val anyState = if (accessors.binarySearch(ANY_ACCESSOR_IDX) >= 0) {
                    treeAnyState[0]
                        ?: manager.anyUnroll.newOrigin(AnyUnrollManager.MINT_DESERIALIZE)
                            .also { treeAnyState[0] = it }
                } else {
                    null
                }

                return manager.create(isAbstract, isFinal, anyFieldAccessorExclusions, accessors, accessNodes, anyState)
            }
        }

        companion object {
            const val SUBSEQUENT_ARRAY_ELEMENTS_LIMIT = 2

            private const val COLLAPSE_NESTED_ANY_PROPERTY = "opentaint.anyCollapseNested"

            /**
             * `-Dopentaint.anyCollapseNested=false` disables the FORCED nested-`[any]` collapse.
             *
             * With it on -- the default -- the normalisation `prependAnyAccessor` always performed
             * is applied at every site that installs an `[any]` edge, so the shape cannot survive a
             * raw spine rebuild, a chain fold, a summary graft or the wire. That is a behavioural
             * change to the representation independent of any budget, and it is a COARSENING rather
             * than the identity the old KDoc claimed, so it is separately switchable in order to be
             * separately measurable.
             */
            @JvmField
            internal val COLLAPSE_NESTED_ANY: Boolean =
                System.getProperty(COLLAPSE_NESTED_ANY_PROPERTY)?.trim()?.toBooleanStrictOrNull() ?: true

            /**
             * The node invariant, applied to a candidate state: keep it exactly when the array it is
             * about to sit on actually holds an `[any]` edge.
             */
            @JvmStatic
            internal fun anyStateIfPresent(accessors: IntArray?, state: AnyUnrollState?): AnyUnrollState? =
                if (state != null && accessors != null && accessors.binarySearch(ANY_ACCESSOR_IDX) >= 0) state else null

            /** Visit budget for [containsThroughAny]. */
            private const val CONTAINS_THROUGH_ANY_STEP_LIMIT = 10_000

            // Bit masks for [flags]. Held as `Int` because Kotlin `Byte` arithmetic promotes to
            // `Int` anyway; the accessors do one `toInt()` (a sign extension, free) and one `and`,
            // which is branch-free, allocation-free and folds away at the call site.
            private const val INTERNED = 1
            private const val ABSTRACT = 1 shl 1
            private const val FINAL = 1 shl 2
            private const val CONTAINS_STATIC = 1 shl 3
            private const val CONTAINS_ANY_DEEP = 1 shl 4

            /**
             * How much a single `[any]` edge adds to [maxDepth].
             *
             * This is a COST charge, not a sentinel: an `[any]` stands for an unbounded sequence of
             * covered steps, so charging it as one step would let a fact carrying it slip past the
             * cost gate in `MethodAnalyzer.edgeExceedLimit` as if it were cheap. It is deliberately
             * small enough that the gate's growing `factDepthLimit` eventually clears it -- a value
             * large enough to make the gate unsatisfiable would park every `[any]`-carrying edge
             * forever.
             *
             * Nothing may use [maxDepth]'s magnitude to decide whether a node carries an `[any]`:
             * that is what [containsAnyInThisOrDeepNodes] is for.
             *
             * The premise side charges an `[any]` link the SAME number, in
             * [AccessPath.AccessNode.depth]. That is deliberate, not a coincidence:
             * `MethodAnalyzer.edgeExceedLimit` gates an edge's premise and its fact against one
             * budget, so a cheaper premise charge would admit premises that no fact matching them
             * can pass. Visibility is `internal` rather than public so only the premise side in this
             * module can share it.
             */
            internal const val ANY_ACCESSOR_DEPTH_CHARGE = 10

            @JvmStatic
            private fun removeSingleAccessor(
                accessor: AccessorIdx,
                accessors: IntArray?,
                nodes: Array<AccessNode>?
            ): Pair<IntArray?, Array<AccessNode>?>? {
                if (accessors == null) {
                    return null
                }
                nodes!!

                val accessorIdx = accessors.binarySearch(accessor)
                if (accessorIdx < 0) return null

                val newAccessorsSize = accessors.size - 1
                if (newAccessorsSize == 0) {
                    return null to null
                }

                val newAccessors = IntArray(newAccessorsSize)
                val newNodes = arrayOfNulls<AccessNode>(newAccessorsSize)

                accessors.copyInto(newAccessors, endIndex = accessorIdx)
                accessors.copyInto(newAccessors, destinationOffset = accessorIdx, startIndex = accessorIdx + 1)

                nodes.copyInto(newNodes, endIndex = accessorIdx)
                nodes.copyInto(newNodes, destinationOffset = accessorIdx, startIndex = accessorIdx + 1)

                @Suppress("UNCHECKED_CAST")
                return newAccessors to newNodes as Array<AccessNode>
            }

            // Adding inline here leads to java.lang.VerifyError, seems to be issue with Kotlin compiler
            @JvmStatic
            private fun transformAccessors(
                accessors: IntArray?,
                nodes: Array<AccessNode>?,
                transformer: (AccessorIdx, AccessNode) -> AccessNode?,
            ): Pair<IntArray, Array<AccessNode>>? {
                if (accessors == null) return null
                nodes!!

                var modified = false
                var accessorsModified = false

                var writeIdx = 0
                val transformedAccessors = IntArray(nodes.size)
                val transformedNodes = arrayOfNulls<AccessNode>(nodes.size)

                for (i in nodes.indices) {
                    val field = accessors[i]
                    val node = nodes[i]

                    val transformedNode = transformer(field, node)
                    if (transformedNode === node) {
                        transformedAccessors[writeIdx] = field
                        transformedNodes[writeIdx] = node
                        writeIdx++
                    } else {
                        modified = true

                        if (transformedNode == null) {
                            accessorsModified = true
                            continue
                        }

                        transformedAccessors[writeIdx] = field
                        transformedNodes[writeIdx] = transformedNode
                        writeIdx++
                    }
                }

                return trimModifiedAccessors(modified, accessorsModified, writeIdx, accessors, transformedAccessors, transformedNodes)
            }

            private fun trimModifiedAccessors(
                modified: Boolean,
                accessorsModified: Boolean,
                writeIdx: Int,
                originalAccessors: IntArray,
                accessors: IntArray,
                nodes: Array<AccessNode?>
            ): Pair<IntArray, Array<AccessNode>>? {
                if (!modified) return null

                if (!accessorsModified) {
                    check(writeIdx == originalAccessors.size) { "Incorrect size" }

                    val trimmedNodes = if (writeIdx == nodes.size) {
                        nodes
                    } else {
                        nodes.copyOf(writeIdx)
                    }

                    @Suppress("UNCHECKED_CAST")
                    return originalAccessors to trimmedNodes as Array<AccessNode>
                }

                if (writeIdx != accessors.size) {
                    val trimmedAccessors = accessors.copyOf(writeIdx)
                    val trimmedNodes = nodes.copyOf(writeIdx)
                    @Suppress("UNCHECKED_CAST")
                    return trimmedAccessors to trimmedNodes as Array<AccessNode>
                } else {
                    @Suppress("UNCHECKED_CAST")
                    return accessors to nodes as Array<AccessNode>
                }
            }

            @JvmStatic
            fun TreeApManager.create(isAbstract: Boolean = false, isFinal: Boolean = false): AccessNode =
                if (isAbstract) {
                    if (isFinal) abstractFinalNode else abstractNode
                } else {
                    if (isFinal) finalNode else emptyNode
                }

            fun createInitialNode(
                manager: TreeApManager,
                isAbstract: Boolean,
                isFinal: Boolean
            ): AccessNode = AccessNode(
                manager,
                interned = true,
                isAbstract = isAbstract, isFinal = isFinal,
                deepAccessorExclusion = null,
                accessors = null, accessorNodes = null,
                anyIdRaw = null,
            )

            @JvmStatic
            private fun TreeApManager.create(elementAccess: AccessNode?, absorbing: Boolean): AccessNode =
                elementAccess?.let { access ->
                    // `limitElementAccess` never returns null, so the element arm DOES go through the
                    // funnel, and `ElementAccessor` is covered -- element absorption is on. The
                    // subtree probe is what makes that safe: `[].[any].[]` is the one
                    // repeated-accessor-across-an-`[any]` shape the engine does not collapse at
                    // construction, because `limitElementAccess` caps only CONSECUTIVE runs.
                    if (absorbing) create(ELEMENT_ACCESSOR_IDX, access) else createRaw(ELEMENT_ACCESSOR_IDX, access)
                } ?: emptyNode

            /**
             * The single-edge build, and the funnel the absorbing prepend lives in.
             *
             * Putting the rule here rather than in one caller covers every caller at once and stays
             * covered as callers are added -- the same structural argument that put the READ record
             * in `getChild`. It serves `reconstructRemainder`, both premise chain folds, and
             * `addParentIfPossible`'s static / mark / type-info / `[value]` arms; the field and
             * element arms reach it too, and they are the two carrying COVERED accessors, so they are
             * exactly the ones that will absorb.
             */
            @JvmStatic
            fun create(accessor: AccessorIdx, node: AccessNode, anyState: AnyUnrollState? = null): AccessNode =
                node.installAbove(accessor, anyState)

            /**
             * [create] without the absorption: today's body, unchanged.
             *
             * Two functions rather than a flag because the initial-fact abstraction must be able to
             * reach `addParentIfPossible` in BOTH modes. Its unroll re-roots the materialised copy
             * and then prepends the accessor it just read, so the backward query would match
             * perfectly, the absorption would fire, and the fold would telescope away the
             * `filterAccessNode` copy it just paid for -- undoing a deliberate enumeration AFTER
             * paying for it.
             */
            @JvmStatic
            fun createRaw(accessor: AccessorIdx, node: AccessNode, anyState: AnyUnrollState? = null): AccessNode {
                // The single choke point for every raw single-edge build, including
                // createAbstractNodeFromReversedAp / createAbstractNodeFromAccessors, which fold an
                // arbitrary accessor chain straight through here. A taint mark is a leaf marker:
                // nothing structured may sit below it, mirroring addParentIfPossible's rule.
                // Consequence: `[any].![m].[any]` is unconstructible, so the nested-`[any]` collapse
                // needs no exception for an intervening taint mark.
                if (accessor.isTaintMarkAccessor()) {
                    check(node.isStructurelessLeaf) {
                        val accessorName = with(node.manager) { accessor.accessor }
                        "Taint mark accessor $accessorName above a structured node: $node"
                    }
                }

                // NOTE a type-info accessor CAN legitimately carry children; only marks are banned,
                // and `{T}.[any]` is a shape the ordinary prepend path builds -- pinned by
                // AnyAccessorCollapseTest's uncovered-accessor case and by AnyPremiseAbstractionTest.
                // So this is deliberately NOT a `check`: an assertion here would ban a legal fact.
                // `[any].{T}.[any]` therefore follows from one more prepend, which is why the
                // union-without-collapse arm below is load-bearing rather than defensive, and why
                // §12.1 counts it by separating accessor rather than assuming it empty.

                if (accessor == ANY_ACCESSOR_IDX) {
                    return createAnyEdge(node, anyState, AnyUnrollManager.MINT_RAW_EDGE)
                }

                return AccessNode(
                    node.manager,
                    interned = false,
                    isAbstract = false, isFinal = false,
                    deepAccessorExclusion = null,
                    accessors = intArrayOf(accessor),
                    accessorNodes = arrayOf(node),
                    anyIdRaw = null,
                )
            }

            /**
             * Install an `[any]` edge over [child], normalising the subtree first.
             *
             * The three rules of the lifecycle meet here. If the caller supplies a state it wins
             * (the receiver-preferred union of R3). If it does not, an `[any]` already present below
             * is REUSED rather than minted (R2) -- minting on a re-prepend is a budget refill, and
             * the fast arm of the normalisation is exactly the O(1) case split that decides which.
             * Only a genuinely fresh `[any]` mints an origin (R1).
             */
            @JvmStatic
            private fun createAnyEdge(
                child: AccessNode,
                installed: AnyUnrollState?,
                mintSite: Int,
            ): AccessNode {
                val manager = child.manager
                val (normalised, found) = child.normaliseUnderAny()

                val state = when {
                    !manager.anyUnroll.enabled -> null
                    installed != null -> manager.anyUnroll.union(installed, found)
                    found != null -> found
                    else -> manager.anyUnroll.newOrigin(mintSite)
                }

                return AccessNode(
                    manager,
                    interned = false,
                    isAbstract = false, isFinal = false,
                    deepAccessorExclusion = null,
                    accessors = intArrayOf(ANY_ACCESSOR_IDX),
                    accessorNodes = arrayOf(normalised),
                    anyIdRaw = state,
                )
            }

            /**
             * The array factory, and the second of the three sites that can install an `[any]` edge.
             *
             * [anyState] is the state for the `[any]` slot of [accessors], if there is one. It is a
             * REQUIRED parameter rather than a defaulted one on purpose: the propagation rule is
             * "every construction passes an explicit state, and `state != null` iff the array holds
             * an `[any]`", and a default would turn a forgotten site into a silent budget refill
             * instead of a compile error.
             */
            @JvmStatic
            fun TreeApManager.create(
                isAbstract: Boolean,
                isFinal: Boolean,
                deepAccessorExclusion: DeepAccessorExclusion?,
                accessors: IntArray?,
                accessorNodes: Array<AccessNode>?,
                anyState: AnyUnrollState?,
            ): AccessNode =
                if (isAbstract) {
                    if (isFinal) {
                        createElementAndField(abstractFinalNode, deepAccessorExclusion, accessors, accessorNodes, anyState)
                    } else {
                        createElementAndField(abstractNode, deepAccessorExclusion, accessors, accessorNodes, anyState)
                    }
                } else {
                    if (isFinal) {
                        createElementAndField(finalNode, deepAccessorExclusion = null, accessors, accessorNodes, anyState)
                    } else {
                        createElementAndField(emptyNode, deepAccessorExclusion = null, accessors, accessorNodes, anyState)
                    }
                }

            @JvmStatic
            private fun createElementAndField(
                base: AccessNode,
                deepAccessorExclusion: DeepAccessorExclusion?,
                accessors: IntArray?,
                accessorNodes: Array<AccessNode>?,
                anyState: AnyUnrollState?,
            ): AccessNode {
                val nonEmptyAccessors = accessors?.takeIf { it.isNotEmpty() }
                val nonEmptyAccessorNodes = accessorNodes?.takeIf { nonEmptyAccessors != null }
                if (nonEmptyAccessors == null && deepAccessorExclusion == null) {
                    // The singleton collapse stays valid: by the node invariant a childless,
                    // exclusion-free node owns no `[any]` edge, so no state can be lost here.
                    return base
                }

                val manager = base.manager
                var resultNodes = nonEmptyAccessorNodes
                var state: AnyUnrollState? = null

                val anyIdx = nonEmptyAccessors?.binarySearch(ANY_ACCESSOR_IDX) ?: -1
                if (anyIdx >= 0) {
                    val child = nonEmptyAccessorNodes!![anyIdx]
                    val (normalised, found) = child.normaliseUnderAny()
                    // The union INVERTS the usual receiver preference on purpose, exactly as
                    // `createAnyEdge` does and for the same reason: the caller-supplied state is the
                    // one the construction is about, and an `[any]` found in the subtree below is the
                    // incumbent being absorbed into it. `bulkMergeAddAccessors` now folds a third
                    // state in here -- the predecessors its pre-pass absorbed into -- and it does so
                    // BEFORE this call, so what arrives as [anyState] is already the accumulated side.
                    state = when {
                        !manager.anyUnroll.enabled -> null
                        anyState != null -> manager.anyUnroll.union(anyState, found)
                        found != null -> found
                        else -> manager.anyUnroll.newOrigin(AnyUnrollManager.MINT_BULK_MERGE)
                    }
                    if (normalised !== child) {
                        // The array is shared with the node it came from; never write through it.
                        resultNodes = nonEmptyAccessorNodes.copyOf()
                        resultNodes[anyIdx] = normalised
                    }
                }

                return AccessNode(
                    manager,
                    interned = false,
                    isAbstract = base.isAbstract,
                    isFinal = base.isFinal,
                    deepAccessorExclusion = deepAccessorExclusion,
                    accessors = nonEmptyAccessors,
                    accessorNodes = resultNodes,
                    anyIdRaw = state,
                )
            }

            /**
             * Fold a premise chain into a linear-spine fact.
             *
             * ONE state for the whole fold, not one per `[any]` link: the chain is linear, so all
             * its `[any]`s lie on a single branch and the branch invariant says they must be one
             * manager anyway. [anyState] is the state the caller's walk was already holding -- the
             * abstraction inherits rather than minting, because minting per emitted premise would
             * restore a per-premise budget, which is the failure the per-context counter was
             * rejected for arriving through a side door.
             */
            /**
             * [create] with the chain-fold absorptions counted separately.
             *
             * Both premise chain folds are census row 1 and go through the funnel. The one that
             * matters is the initial-fact abstraction's emission, where read and prepend are
             * co-located exactly as they are in `filterStartsWith` -- so the rule fires, and firing
             * UNDOES the enumeration the abstraction just paid for. Sound, but the same shape the
             * abstraction's OTHER prepend is excluded for, so it is measured rather than assumed.
             */
            @JvmStatic
            private fun createCountingChainFold(accessor: AccessorIdx, node: AccessNode): AccessNode {
                if (!AnyUnrollDiagnostics.enabled) return create(accessor, node)
                val before = AnyUnrollDiagnostics.absorptions.get()
                val result = create(accessor, node)
                if (AnyUnrollDiagnostics.absorptions.get() != before) {
                    AnyUnrollDiagnostics.chainFoldAbsorbs.incrementAndGet()
                }
                return result
            }

            @JvmStatic
            fun TreeApManager.createAbstractNodeFromReversedAp(
                reversedAp: ReversedApNode?,
                anyState: AnyUnrollState? = null,
            ): AccessNode {
                var foldState = anyState
                return reversedAp.foldRight(abstractNode) { accessor, node ->
                    when (accessor) {
                        FINAL_ACCESSOR_IDX -> finalNode
                        ANY_ACCESSOR_IDX -> {
                            if (foldState == null) foldState = anyUnroll.newOrigin(AnyUnrollManager.MINT_RAW_EDGE)
                            create(accessor, node, foldState)
                        }
                        else -> createCountingChainFold(accessor, node)
                    }
                }
            }

            @JvmStatic
            fun TreeApManager.createAbstractNodeFromAccessors(
                accessors: IntList,
                anyState: AnyUnrollState? = null,
            ): AccessNode {
                var result = abstractNode
                var foldState = anyState
                accessors.reversedForEachInt { accessor ->
                    result = when (accessor) {
                        FINAL_ACCESSOR_IDX -> finalNode
                        ANY_ACCESSOR_IDX -> {
                            if (foldState == null) foldState = anyUnroll.newOrigin(AnyUnrollManager.MINT_RAW_EDGE)
                            create(accessor, result, foldState)
                        }
                        else -> createCountingChainFold(accessor, result)
                    }
                }

                return result
            }

            private fun <K, V: Any> Object2ObjectOpenHashMap<K, V>.getComputedResult(key: K): V =
                get(key) ?: error("Result for $key was not computed")

            private val NodeExpansionRequested = Any()
        }
    }
}

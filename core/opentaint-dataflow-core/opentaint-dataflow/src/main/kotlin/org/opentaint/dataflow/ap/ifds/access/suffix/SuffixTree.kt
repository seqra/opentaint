package org.opentaint.dataflow.ap.ifds.access.suffix

/**
 * Immutable language of shared suffix cones.
 *
 * A terminal at path [p] with exclusions [e] denotes `p.s`, where `s` is empty or its first
 * accessor is not in [e]. A tree is the union of all of its terminal cones.
 */
class SuffixTree private constructor(val root: Node) {
    @ConsistentCopyVisibility
    data class Node internal constructor(
        /** `null` means that this node is not terminal; an empty set is a full wildcard terminal. */
        val exclusions: Set<Int>?,
        val children: Map<Int, Node>,
    ) {
        val isTerminal: Boolean get() = exclusions != null
    }

    data class Cone(val suffix: List<Int>, val exclusions: Set<Int>)

    fun cones(): List<Cone> = buildList {
        fun visit(node: Node, path: MutableList<Int>) {
            node.exclusions?.let { add(Cone(path.toList(), it)) }
            for ((accessor, child) in node.children) {
                path.add(accessor)
                visit(child, path)
                path.removeAt(path.lastIndex)
            }
        }
        visit(root, ArrayList())
    }

    fun hasNonEmptySuffix(): Boolean = cones().any { it.suffix.isNotEmpty() }

    fun isBranching(): Boolean {
        fun visit(node: Node): Boolean =
            node.children.size > 1 || node.children.values.any(::visit)
        return visit(root)
    }

    override fun equals(other: Any?): Boolean =
        this === other || other is SuffixTree && root == other.root

    override fun hashCode(): Int = root.hashCode()

    internal companion object {
        fun fromCones(cones: List<Cone>): SuffixTree {
            class MutableNode {
                var exclusions: Set<Int>? = null
                val children = HashMap<Int, MutableNode>()
            }

            val mutableRoot = MutableNode()
            for (cone in cones) {
                var node = mutableRoot
                for (accessor in cone.suffix) {
                    node = node.children.getOrPut(accessor, ::MutableNode)
                }
                check(node.exclusions == null) { "Duplicate canonical suffix terminal: ${cone.suffix}" }
                node.exclusions = cone.exclusions.toSet()
            }

            fun freeze(node: MutableNode): Node = Node(
                exclusions = node.exclusions,
                children = node.children.mapValues { freeze(it.value) },
            )
            return SuffixTree(freeze(mutableRoot))
        }
    }
}

/** The final-prefix leaf markers retained when an [org.opentaint.dataflow.ap.ifds.access.tree.AccessTree] is decomposed. */
data class FinalPrefixMarkers(val isFinal: Boolean, val isAbstract: Boolean)

/**
 * Immutable final-prefix access tree. Every terminal is paired diagonally with every cone in the
 * surrounding [SuffixEdgeBundle]. Branches are merged only when they have the same suffix
 * language, so traversing this tree cannot manufacture a cross product that was not stored.
 */
class FinalPrefixTree private constructor(val root: Node) {
    @ConsistentCopyVisibility
    data class Node internal constructor(
        val isFinal: Boolean,
        val isAbstract: Boolean,
        val children: Map<Int, Node>,
    ) {
        val isTerminal: Boolean get() = isFinal || isAbstract
    }

    data class Terminal(val prefix: List<Int>, val markers: FinalPrefixMarkers)

    fun terminals(): List<Terminal> = buildList {
        val path = ArrayList<Int>()
        fun visit(node: Node) {
            if (node.isTerminal) {
                add(Terminal(path.toList(), FinalPrefixMarkers(node.isFinal, node.isAbstract)))
            }
            for ((accessor, child) in node.children) {
                path.add(accessor)
                visit(child)
                path.removeAt(path.lastIndex)
            }
        }
        visit(root)
    }

    fun isBranching(): Boolean {
        fun visit(node: Node): Boolean =
            node.children.size > 1 || node.children.values.any(::visit)
        return visit(root)
    }

    fun isSingle(prefix: List<Int>): Boolean {
        val terminals = terminals()
        return terminals.size == 1 && terminals.single().prefix == prefix
    }

    override fun equals(other: Any?): Boolean =
        this === other || other is FinalPrefixTree && root == other.root

    override fun hashCode(): Int = root.hashCode()

    internal companion object {
        fun fromTerminals(terminals: Iterable<Terminal>): FinalPrefixTree {
            class MutableNode {
                var isFinal = false
                var isAbstract = false
                val children = LinkedHashMap<Int, MutableNode>()
            }

            val mutableRoot = MutableNode()
            var terminalCount = 0
            for ((prefix, markers) in terminals) {
                var node = mutableRoot
                for (accessor in prefix) {
                    node = node.children.getOrPut(accessor, ::MutableNode)
                }
                node.isFinal = node.isFinal || markers.isFinal
                node.isAbstract = node.isAbstract || markers.isAbstract
                terminalCount++
            }
            check(terminalCount > 0) { "A final-prefix tree must have a terminal" }

            fun freeze(node: MutableNode): Node = Node(
                isFinal = node.isFinal,
                isAbstract = node.isAbstract,
                children = node.children.mapValues { freeze(it.value) },
            )
            return FinalPrefixTree(freeze(mutableRoot))
        }

        fun single(prefix: List<Int>, markers: FinalPrefixMarkers): FinalPrefixTree =
            fromTerminals(listOf(Terminal(prefix, markers)))
    }
}

/** One maximally factored canonical generator. */
data class SuffixGenerator(
    val initialPrefix: List<Int>,
    val finalPrefix: List<Int>,
    val suffix: List<Int>,
    val exclusions: Set<Int>,
    val finalMarkers: FinalPrefixMarkers = FinalPrefixMarkers(isFinal = false, isAbstract = true),
)

/**
 * One edge bundle. Every cone in [suffixTree] is appended diagonally to [initialPrefix] and every
 * leaf of [finalPrefixTree]. Final-prefix branches are grouped only when their complete suffix
 * languages are equal, so the represented cross product consists exclusively of stored edges.
 */
data class SuffixEdgeBundle(
    val initialPrefix: List<Int>,
    val finalPrefixTree: FinalPrefixTree,
    val suffixTree: SuffixTree,
) {
    fun isIdentityForSameBase(): Boolean = finalPrefixTree.isSingle(initialPrefix)
}

/** Canonicalize only the newly added generators for delta publication. */
internal fun suffixDeltaBundles(generators: Iterable<SuffixGenerator>): List<SuffixEdgeBundle> {
    val delta = SuffixRelationTrie()
    generators.forEach { delta.add(it) }
    return delta.bundles()
}

/**
 * Mutable canonical relation used by SuffixTree stores.
 *
 * Layout: initial-prefix trie -> suffix trie -> final-prefix trie. The suffix trie is primary below
 * one initial prefix, so equal suffix paths are physically shared by all final prefixes. Published
 * [bundles] group all suffix cones of an exact prefix pair into one edge-level [SuffixTree].
 */
class SuffixRelationTrie {
    private class FinalPrefixNode {
        class Terminal(var exclusions: HashSet<Int>)

        val children = HashMap<Int, FinalPrefixNode>()
        private val terminals = HashMap<FinalPrefixMarkers, Terminal>()

        fun lookup(prefix: List<Int>, markers: FinalPrefixMarkers): Terminal? {
            var node = this
            for (accessor in prefix) node = node.children[accessor] ?: return null
            return node.terminals[markers]
        }

        fun put(prefix: List<Int>, markers: FinalPrefixMarkers, exclusions: Set<Int>): Terminal {
            var node = this
            for (accessor in prefix) node = node.children.getOrPut(accessor, ::FinalPrefixNode)
            return node.terminals.getOrPut(markers) { Terminal(HashSet(exclusions)) }
        }

        fun remove(prefix: List<Int>, markers: FinalPrefixMarkers) {
            fun removeAt(node: FinalPrefixNode, index: Int): Boolean {
                if (index == prefix.size) {
                    node.terminals.remove(markers)
                } else {
                    val accessor = prefix[index]
                    val child = node.children[accessor] ?: return node.isEmpty()
                    if (removeAt(child, index + 1)) node.children.remove(accessor)
                }
                return node.isEmpty()
            }
            removeAt(this, 0)
        }

        fun forEach(action: (List<Int>, FinalPrefixMarkers, Terminal) -> Unit) {
            val path = ArrayList<Int>()
            fun visit(node: FinalPrefixNode) {
                for ((markers, terminal) in node.terminals) action(path.toList(), markers, terminal)
                for ((accessor, child) in node.children) {
                    path.add(accessor)
                    visit(child)
                    path.removeAt(path.lastIndex)
                }
            }
            visit(this)
        }

        fun isEmpty(): Boolean = terminals.isEmpty() && children.isEmpty()
    }

    private class MutableSuffixNode {
        val children = HashMap<Int, MutableSuffixNode>()
        val finalPrefixes = FinalPrefixNode()
        fun isDead(): Boolean = children.isEmpty() && finalPrefixes.isEmpty()
    }

    private class InitialPrefixNode {
        val children = HashMap<Int, InitialPrefixNode>()
        var suffixRoot: MutableSuffixNode? = null
    }

    private val initialRoot = InitialPrefixNode()

    /** True once two separately represented cones have been folded into a wider cone. */
    var hasSquashed: Boolean = false
        private set

    /** Maximal common-suffix factoring. */
    fun factor(
        initialPath: IntArray,
        finalPath: IntArray,
        exclusions: Set<Int>,
        finalMarkers: FinalPrefixMarkers = FinalPrefixMarkers(isFinal = false, isAbstract = true),
    ): SuffixGenerator {
        var commonLength = 0
        while (
            commonLength < initialPath.size && commonLength < finalPath.size &&
            initialPath[initialPath.lastIndex - commonLength] == finalPath[finalPath.lastIndex - commonLength]
        ) {
            commonLength++
        }
        return SuffixGenerator(
            initialPrefix = initialPath.copyOfRange(0, initialPath.size - commonLength).toList(),
            finalPrefix = finalPath.copyOfRange(0, finalPath.size - commonLength).toList(),
            suffix = initialPath.copyOfRange(initialPath.size - commonLength, initialPath.size).toList(),
            exclusions = exclusions.toSet(),
            finalMarkers = finalMarkers,
        )
    }

    /** Returns true exactly when the relation language grew. */
    fun add(
        initialPath: IntArray,
        finalPath: IntArray,
        exclusions: Set<Int>,
        finalMarkers: FinalPrefixMarkers = FinalPrefixMarkers(isFinal = false, isAbstract = true),
    ): Boolean = add(factor(initialPath, finalPath, exclusions, finalMarkers))

    /** Returns true exactly when the relation language grew. */
    fun add(generator: SuffixGenerator): Boolean {
        if (coversCone(generator)) return false
        insertCone(generator)
        return true
    }

    fun isCovered(generator: SuffixGenerator): Boolean = coversCone(generator)

    fun containsPair(
        initialPath: IntArray,
        finalPath: IntArray,
        finalMarkers: FinalPrefixMarkers = FinalPrefixMarkers(isFinal = false, isAbstract = true),
    ): Boolean {
        val generator = factor(initialPath, finalPath, emptySet(), finalMarkers)
        return containsSuffix(
            generator.initialPrefix,
            generator.finalPrefix,
            generator.finalMarkers,
            generator.suffix,
        )
    }

    fun generators(): List<SuffixGenerator> = buildList {
        forEachInitialPrefix { initialPrefix, suffixRoot ->
            val suffix = ArrayList<Int>()
            fun visit(node: MutableSuffixNode) {
                node.finalPrefixes.forEach { finalPrefix, markers, terminal ->
                    add(
                        SuffixGenerator(
                            initialPrefix,
                            finalPrefix,
                            suffix.toList(),
                            terminal.exclusions.toSet(),
                            markers,
                        )
                    )
                }
                for ((accessor, child) in node.children) {
                    suffix.add(accessor)
                    visit(child)
                    suffix.removeAt(suffix.lastIndex)
                }
            }
            visit(suffixRoot)
        }
    }

    /**
     * Groups equal suffix languages under a final-prefix access tree. In particular, all identity
     * relations sharing a base cell and prefix are folded into one branching suffix tree.
     */
    fun bundles(): List<SuffixEdgeBundle> {
        data class ExactPrefixKey(
            val initialPrefix: List<Int>,
            val finalPrefix: List<Int>,
            val markers: FinalPrefixMarkers,
        )
        data class BundleKey(
            val initialPrefix: List<Int>,
            val suffixTree: SuffixTree,
        )

        val exactPrefixes = LinkedHashMap<ExactPrefixKey, MutableList<SuffixTree.Cone>>()
        for (generator in generators()) {
            val key = ExactPrefixKey(
                generator.initialPrefix,
                generator.finalPrefix,
                generator.finalMarkers,
            )
            exactPrefixes.getOrPut(key, ::ArrayList).add(
                SuffixTree.Cone(generator.suffix, generator.exclusions)
            )
        }

        val grouped = LinkedHashMap<BundleKey, MutableList<FinalPrefixTree.Terminal>>()
        for ((key, cones) in exactPrefixes) {
            val bundleKey = BundleKey(key.initialPrefix, SuffixTree.fromCones(cones))
            grouped.getOrPut(bundleKey, ::ArrayList).add(
                FinalPrefixTree.Terminal(key.finalPrefix, key.markers)
            )
        }
        return grouped.map { (key, finalPrefixes) ->
            SuffixEdgeBundle(
                key.initialPrefix,
                FinalPrefixTree.fromTerminals(finalPrefixes),
                key.suffixTree,
            )
        }
    }

    fun checkInvariants() {
        forEachInitialPrefix { initialPrefix, suffixRoot ->
            check(!suffixRoot.isDead()) { "Dead suffix root for initial prefix $initialPrefix" }
            checkSuffixNode(initialPrefix, emptyList(), suffixRoot)
        }
    }

    private fun coversCone(generator: SuffixGenerator): Boolean {
        var node = suffixRootFor(generator.initialPrefix) ?: return false
        for ((index, accessor) in generator.suffix.withIndex()) {
            val terminal = node.finalPrefixes.lookup(generator.finalPrefix, generator.finalMarkers)
            if (terminal != null && accessor !in terminal.exclusions) return true
            node = node.children[accessor] ?: return false
        }

        val terminal = node.finalPrefixes.lookup(generator.finalPrefix, generator.finalMarkers)
            ?: return false
        for (excludedAccessor in terminal.exclusions) {
            if (excludedAccessor in generator.exclusions) continue
            val childTerminal = node.children[excludedAccessor]
                ?.finalPrefixes
                ?.lookup(generator.finalPrefix, generator.finalMarkers)
            if (childTerminal == null || childTerminal.exclusions.isNotEmpty()) return false
        }
        return true
    }

    private fun containsSuffix(
        initialPrefix: List<Int>,
        finalPrefix: List<Int>,
        markers: FinalPrefixMarkers,
        suffix: List<Int>,
    ): Boolean {
        var node = suffixRootFor(initialPrefix) ?: return false
        for (accessor in suffix) {
            val terminal = node.finalPrefixes.lookup(finalPrefix, markers)
            if (terminal != null && accessor !in terminal.exclusions) return true
            node = node.children[accessor] ?: return false
        }
        return node.finalPrefixes.lookup(finalPrefix, markers) != null
    }

    private fun insertCone(generator: SuffixGenerator) {
        val root = suffixRootForCreate(generator.initialPrefix)
        val path = ArrayList<MutableSuffixNode>(generator.suffix.size + 1)
        path.add(root)
        var node = root
        for (accessor in generator.suffix) {
            node = node.children.getOrPut(accessor, ::MutableSuffixNode)
            path.add(node)
        }

        val existing = node.finalPrefixes.lookup(generator.finalPrefix, generator.finalMarkers)
        val mergedExclusions = if (existing == null) {
            node.finalPrefixes.put(
                generator.finalPrefix,
                generator.finalMarkers,
                generator.exclusions,
            ).exclusions
        } else {
            if (existing.exclusions != generator.exclusions &&
                !generator.exclusions.containsAll(existing.exclusions)
            ) {
                hasSquashed = true
            }
            existing.exclusions.retainAll(generator.exclusions)
            existing.exclusions
        }

        val purge = node.children.keys.filter { it !in mergedExclusions }
        for (accessor in purge) {
            val child = node.children.getValue(accessor)
            if (removeFinalPrefix(child, generator.finalPrefix, generator.finalMarkers)) {
                node.children.remove(accessor)
            }
        }

        val absorb = mergedExclusions.filter { accessor ->
            node.children[accessor]
                ?.finalPrefixes
                ?.lookup(generator.finalPrefix, generator.finalMarkers)
                ?.exclusions
                ?.isEmpty() == true
        }
        for (accessor in absorb) {
            hasSquashed = true
            mergedExclusions.remove(accessor)
            val child = node.children.getValue(accessor)
            if (removeFinalPrefix(child, generator.finalPrefix, generator.finalMarkers)) {
                node.children.remove(accessor)
            }
        }

        var index = path.lastIndex
        while (index >= 1) {
            val current = path[index]
            val currentTerminal = current.finalPrefixes.lookup(generator.finalPrefix, generator.finalMarkers)
            if (currentTerminal == null || currentTerminal.exclusions.isNotEmpty()) break

            val parent = path[index - 1]
            val edgeAccessor = generator.suffix[index - 1]
            val parentTerminal = parent.finalPrefixes.lookup(generator.finalPrefix, generator.finalMarkers)
            if (parentTerminal == null || edgeAccessor !in parentTerminal.exclusions) break

            hasSquashed = true
            parentTerminal.exclusions.remove(edgeAccessor)
            current.finalPrefixes.remove(generator.finalPrefix, generator.finalMarkers)
            if (current.isDead()) parent.children.remove(edgeAccessor)
            index--
        }
    }

    private fun removeFinalPrefix(
        node: MutableSuffixNode,
        finalPrefix: List<Int>,
        markers: FinalPrefixMarkers,
    ): Boolean {
        node.finalPrefixes.remove(finalPrefix, markers)
        val iterator = node.children.entries.iterator()
        while (iterator.hasNext()) {
            val child = iterator.next().value
            if (removeFinalPrefix(child, finalPrefix, markers)) iterator.remove()
        }
        return node.isDead()
    }

    private fun checkSuffixNode(
        initialPrefix: List<Int>,
        suffix: List<Int>,
        node: MutableSuffixNode,
    ) {
        for ((accessor, child) in node.children) {
            check(!child.isDead()) {
                "Dead suffix child $accessor at initial=$initialPrefix suffix=$suffix"
            }
        }

        node.finalPrefixes.forEach { finalPrefix, markers, terminal ->
            for ((accessor, child) in node.children) {
                if (accessor !in terminal.exclusions) {
                    check(!subtreeHasFinalPrefix(child, finalPrefix, markers)) {
                        "Redundant final prefix $finalPrefix below open accessor $accessor at " +
                            "initial=$initialPrefix suffix=$suffix"
                    }
                } else {
                    val childTerminal = child.finalPrefixes.lookup(finalPrefix, markers)
                    check(childTerminal == null || childTerminal.exclusions.isNotEmpty()) {
                        "Unannihilated full-wildcard child for final prefix $finalPrefix via $accessor at " +
                            "initial=$initialPrefix suffix=$suffix"
                    }
                }
            }
        }

        for ((accessor, child) in node.children) {
            checkSuffixNode(initialPrefix, suffix + accessor, child)
        }
    }

    private fun subtreeHasFinalPrefix(
        node: MutableSuffixNode,
        finalPrefix: List<Int>,
        markers: FinalPrefixMarkers,
    ): Boolean {
        if (node.finalPrefixes.lookup(finalPrefix, markers) != null) return true
        return node.children.values.any { subtreeHasFinalPrefix(it, finalPrefix, markers) }
    }

    private fun suffixRootFor(initialPrefix: List<Int>): MutableSuffixNode? {
        var node = initialRoot
        for (accessor in initialPrefix) node = node.children[accessor] ?: return null
        return node.suffixRoot
    }

    private fun suffixRootForCreate(initialPrefix: List<Int>): MutableSuffixNode {
        var node = initialRoot
        for (accessor in initialPrefix) node = node.children.getOrPut(accessor, ::InitialPrefixNode)
        return node.suffixRoot ?: MutableSuffixNode().also { node.suffixRoot = it }
    }

    private fun forEachInitialPrefix(action: (List<Int>, MutableSuffixNode) -> Unit) {
        val path = ArrayList<Int>()
        fun visit(node: InitialPrefixNode) {
            node.suffixRoot?.let { action(path.toList(), it) }
            for ((accessor, child) in node.children) {
                path.add(accessor)
                visit(child)
                path.removeAt(path.lastIndex)
            }
        }
        visit(initialRoot)
    }
}

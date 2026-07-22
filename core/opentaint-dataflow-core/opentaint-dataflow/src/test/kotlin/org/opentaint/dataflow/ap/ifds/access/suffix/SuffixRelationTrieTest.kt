package org.opentaint.dataflow.ap.ifds.access.suffix

import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class SuffixRelationTrieTest {
    @Test
    fun `maximal common suffix is factored`() {
        val trie = SuffixRelationTrie()
        val generator = trie.factor(
            initialPath = intArrayOf(1, 2, 3, 4),
            finalPath = intArrayOf(9, 2, 3, 4),
            exclusions = setOf(7),
        )

        assertEquals(listOf(1), generator.initialPrefix)
        assertEquals(listOf(9), generator.finalPrefix)
        assertEquals(listOf(2, 3, 4), generator.suffix)
        assertEquals(setOf(7), generator.exclusions)
    }

    @Test
    fun `annihilation works in both insertion directions`() {
        fun assertCanonical(order: List<Triple<IntArray, IntArray, Set<Int>>>) {
            val trie = SuffixRelationTrie()
            for ((initial, final, exclusions) in order) {
                assertTrue(trie.add(initial, final, exclusions))
                trie.checkInvariants()
            }

            assertEquals(
                setOf(
                    SuffixGenerator(
                        initialPrefix = emptyList(),
                        finalPrefix = emptyList(),
                        suffix = listOf(1),
                        exclusions = emptySet(),
                    )
                ),
                trie.generators().toSet(),
            )
        }

        val excludingParent = Triple(intArrayOf(1), intArrayOf(1), setOf(2))
        val openChild = Triple(intArrayOf(1, 2), intArrayOf(1, 2), emptySet<Int>())
        assertCanonical(listOf(excludingParent, openChild))
        assertCanonical(listOf(openChild, excludingParent))
    }

    @Test
    fun `identity edges with a common prefix pair form one branching suffix bundle`() {
        val trie = SuffixRelationTrie()
        assertTrue(trie.add(intArrayOf(10, 1), intArrayOf(10, 1), emptySet()))
        assertTrue(trie.add(intArrayOf(10, 2), intArrayOf(10, 2), emptySet()))

        val bundle = trie.bundles().single()
        assertEquals(emptyList(), bundle.initialPrefix)
        assertTrue(bundle.finalPrefixTree.isSingle(emptyList()))
        assertEquals(
            setOf(listOf(10, 1), listOf(10, 2)),
            bundle.suffixTree.cones().mapTo(hashSetOf()) { it.suffix },
        )
        assertTrue(bundle.suffixTree.hasNonEmptySuffix())
        assertTrue(bundle.suffixTree.isBranching())
    }

    @Test
    fun `equal suffix languages share a branching final prefix tree`() {
        val trie = SuffixRelationTrie()
        trie.add(intArrayOf(1, 7), intArrayOf(2, 7), emptySet())
        trie.add(intArrayOf(1, 7), intArrayOf(3, 7), emptySet())

        val bundle = trie.bundles().single()
        assertEquals(listOf(1), bundle.initialPrefix)
        assertEquals(
            setOf(listOf(2), listOf(3)),
            bundle.finalPrefixTree.terminals().mapTo(hashSetOf()) { it.prefix },
        )
        assertTrue(bundle.finalPrefixTree.isBranching())
        assertEquals(listOf(listOf(7)), bundle.suffixTree.cones().map { it.suffix })
    }

    @Test
    fun `different final prefixes do not become a cross product`() {
        val trie = SuffixRelationTrie()
        trie.add(intArrayOf(1, 7), intArrayOf(2, 7), emptySet())
        trie.add(intArrayOf(1, 8), intArrayOf(3, 8), emptySet())

        assertEquals(2, trie.bundles().size)
        assertTrue(trie.containsPair(intArrayOf(1, 7), intArrayOf(2, 7)))
        assertTrue(trie.containsPair(intArrayOf(1, 8), intArrayOf(3, 8)))
        assertFalse(trie.containsPair(intArrayOf(1, 7), intArrayOf(3, 7)))
        assertFalse(trie.containsPair(intArrayOf(1, 8), intArrayOf(2, 8)))
    }

    @Test
    fun `random insertion agrees with an independent bounded oracle`() {
        val alphabet = listOf(0, 1, 2)
        val fresh = 9
        val witnessDepth = 5

        repeat(6) { seed ->
            val random = Random(seed)
            val trie = SuffixRelationTrie()
            val oracle = Oracle(alphabet, fresh, witnessDepth)
            val inserted = ArrayList<Oracle.RawGenerator>()

            repeat(250) { step ->
                val generator = randomGenerator(random, alphabet)
                val expectedNew = oracle.isNew(generator)
                val actualNew = trie.add(generator.initial, generator.final, generator.exclusions)
                assertEquals(
                    expectedNew,
                    actualNew,
                    "seed=$seed step=$step generator=$generator",
                )
                oracle.add(generator)
                inserted.add(generator)
                if (step % 20 == 0) trie.checkInvariants()
            }
            trie.checkInvariants()

            for (generator in inserted) {
                assertTrue(
                    trie.isCovered(
                        trie.factor(generator.initial, generator.final, generator.exclusions)
                    )
                )
                assertFalse(trie.add(generator.initial, generator.final, generator.exclusions))
            }

            repeat(2_000) {
                val initial = randomWord(random, alphabet + fresh, maxLength = 5)
                val final = randomWord(random, alphabet + fresh, maxLength = 5)
                assertEquals(
                    oracle.containsPair(initial, final),
                    trie.containsPair(initial, final),
                    "seed=$seed pair=${initial.toList()} -> ${final.toList()}",
                )
            }
        }
    }

    @Test
    fun `canonical generators are insertion order independent`() {
        val random = Random(777)
        val alphabet = listOf(0, 1, 2)
        val input = List(80) { randomGenerator(random, alphabet) }

        fun build(order: List<Oracle.RawGenerator>): Set<SuffixGenerator> {
            val trie = SuffixRelationTrie()
            for (generator in order) trie.add(generator.initial, generator.final, generator.exclusions)
            trie.checkInvariants()
            return trie.generators().toSet()
        }

        val expected = build(input)
        assertEquals(expected, build(input.shuffled(Random(1))))
        assertEquals(expected, build(input.shuffled(Random(2))))
    }

    private fun randomGenerator(random: Random, alphabet: List<Int>): Oracle.RawGenerator {
        val prefixes = listOf(
            intArrayOf(), intArrayOf(0), intArrayOf(1), intArrayOf(0, 1), intArrayOf(1, 0),
        )
        val suffixes = listOf(
            intArrayOf(), intArrayOf(0), intArrayOf(1), intArrayOf(2), intArrayOf(0, 1),
            intArrayOf(1, 2), intArrayOf(0, 1, 2),
        )
        val initial: IntArray
        val final: IntArray
        if (random.nextBoolean()) {
            val suffix = suffixes.random(random)
            initial = prefixes.random(random) + suffix
            final = prefixes.random(random) + suffix
        } else {
            initial = randomWord(random, alphabet, 4)
            final = randomWord(random, alphabet, 4)
        }
        val exclusions = if (random.nextInt(10) < 4) {
            emptySet()
        } else {
            alphabet.filterTo(hashSetOf()) { random.nextBoolean() }
        }
        return Oracle.RawGenerator(initial, final, exclusions)
    }

    private fun randomWord(random: Random, alphabet: List<Int>, maxLength: Int): IntArray =
        IntArray(random.nextInt(maxLength + 1)) { alphabet.random(random) }

    private class Oracle(
        alphabet: List<Int>,
        fresh: Int,
        private val witnessDepth: Int,
    ) {
        data class RawGenerator(
            val initial: IntArray,
            val final: IntArray,
            val exclusions: Set<Int>,
        ) {
            override fun toString(): String =
                "${initial.toList()} -> ${final.toList()} \\ $exclusions"
        }

        private val alphabet = alphabet + fresh
        private val generators = ArrayList<RawGenerator>()

        fun add(generator: RawGenerator) {
            generators.add(generator)
        }

        fun containsPair(initial: IntArray, final: IntArray): Boolean =
            generators.any { produces(it, initial, final) }

        fun isNew(generator: RawGenerator): Boolean =
            tails(generator.exclusions).any { suffix ->
                !containsPair(generator.initial + suffix, generator.final + suffix)
            }

        private fun produces(generator: RawGenerator, initial: IntArray, final: IntArray): Boolean {
            if (!initial.startsWith(generator.initial) || !final.startsWith(generator.final)) return false
            val initialSuffix = initial.copyOfRange(generator.initial.size, initial.size)
            val finalSuffix = final.copyOfRange(generator.final.size, final.size)
            if (!initialSuffix.contentEquals(finalSuffix)) return false
            return initialSuffix.isEmpty() || initialSuffix.first() !in generator.exclusions
        }

        private fun tails(exclusions: Set<Int>): List<IntArray> = buildList {
            add(intArrayOf())
            var frontier = alphabet.filter { it !in exclusions }.map { intArrayOf(it) }
            var length = 1
            while (length <= witnessDepth) {
                addAll(frontier)
                if (length < witnessDepth) {
                    frontier = frontier.flatMap { prefix -> alphabet.map { prefix + it } }
                }
                length++
            }
        }

        private fun IntArray.startsWith(prefix: IntArray): Boolean {
            if (size < prefix.size) return false
            for (index in prefix.indices) if (this[index] != prefix[index]) return false
            return true
        }
    }
}

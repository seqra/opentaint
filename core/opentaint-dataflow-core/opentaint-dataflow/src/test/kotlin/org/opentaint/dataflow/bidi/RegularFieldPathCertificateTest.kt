package org.opentaint.dataflow.bidi

import kotlin.test.*

/** Read-only proposal oracle. These are finite word automata, not AP facts,
 * analyzer summaries, new field tails or suffix evidence on call packets. */
internal object RegularFieldPathQuery {
    data class Clause(val owner: Int, val word: List<Int>, val next: Int?)
    data class Arc(val from: Int, val symbol: Int, val to: Int)
    data class Nfa(val start: Int, val finals: Set<Int>, val arcs: List<Arc>) {
        fun ends(from: Int, word: List<Int>) = word.fold(setOf(from)) { states, symbol ->
            arcs.asSequence().filter { it.from in states && it.symbol == symbol }.map { it.to }.toSet()
        }
        fun validates(clauses: List<Clause>) = clauses.all { c ->
            val reached = ends(c.owner, c.word)
            if (c.next == null) reached.any { it in finals } else c.next in reached
        }
    }
    data class Proof(val empty: Boolean, val states: Set<Pair<Int,Int>>, val queueOffers: Int)
    fun compile(owners: Int, clauses: List<Clause>): Nfa? {
        if (owners <= 0) return null
        if (clauses.any { it.owner !in 0 until owners || it.next?.let { next -> next !in 0 until owners } == true }) return null
        val final = owners
        var fresh = final + 1
        val finals = linkedSetOf(final)
        val arcs = arrayListOf<Arc>()
        for (c in clauses) {
            if (c.word.isEmpty()) {
                if (c.next == null) finals += c.owner
                else if (c.next != c.owner) return null // no unproved epsilon elimination
                continue
            }
            var from = c.owner
            c.word.forEachIndexed { index, symbol ->
                val to = if (index == c.word.lastIndex) c.next ?: final else fresh++
                arcs += Arc(from,symbol,to)
                from = to
            }
        }
        return Nfa(0,finals,arcs).takeIf { it.validates(clauses) }
    }
    fun query(a: Nfa, b: Nfa): Proof {
        val left = a.arcs.groupBy { it.from }
        val right = b.arcs.groupBy { it.from }
        val start = a.start to b.start
        val seen = linkedSetOf(start)
        val queue = ArrayDeque(listOf(start))
        var offers = 1
        while (queue.isNotEmpty()) {
            val (p,r) = queue.removeFirst()
            for (x in left[p].orEmpty()) for (y in right[r].orEmpty()) if (x.symbol == y.symbol) {
                val next = x.to to y.to
                if (seen.add(next)) { queue.addLast(next); offers++ }
            }
        }
        check(offers == seen.size)
        return Proof(seen.none { it.first in a.finals && it.second in b.finals },seen,offers)
    }
    fun grammar(base: List<Int>, repeat: List<List<Int>>) = listOf(Clause(0,base,null)) + repeat.map { Clause(0,it,0) }
    fun disjoint(w: List<Clause>, r: List<Clause>, owners: Int = 1, completeSlice: Boolean = true): Boolean? {
        if (!completeSlice) return null
        val a = compile(owners,w) ?: return null
        val b = compile(owners,r) ?: return null
        return query(a,b).empty
    }
}

class RegularFieldPathCertificateTest {
    private val f = 1; private val g = 2; private val h = 3
    private fun grammar(base: List<Int>, repeat: List<List<Int>>) = RegularFieldPathQuery.grammar(base,repeat)
    @Test fun `nondeterministic writer and reader ending at different fields are disjoint`() {
        assertEquals(true,RegularFieldPathQuery.disjoint(grammar(listOf(f),listOf(listOf(g),listOf(h))),grammar(listOf(g),listOf(listOf(g),listOf(h)))))
    }
    @Test fun `same last field needs the complete terminal chunk`() {
        assertEquals(true,RegularFieldPathQuery.disjoint(grammar(listOf(f,h),listOf(listOf(g),listOf(h))),grammar(listOf(g,h),listOf(listOf(g),listOf(h)))))
    }
    @Test fun `parity distinguishes paths with all the same final fields`() {
        assertEquals(true,RegularFieldPathQuery.disjoint(grammar(listOf(f),listOf(listOf(g,g))),grammar(listOf(g,f),listOf(listOf(g,g)))))
    }
    @Test fun `a long shared word prevents empty certification`() {
        val a = grammar(listOf(f),listOf(listOf(g,g)))
        val b = grammar(listOf(g,g,g,g,f),listOf(listOf(h)))
        assertEquals(false,RegularFieldPathQuery.disjoint(a,b))
    }
    @Test fun `observer suffix belongs in the consumer language`() {
        assertEquals(false,RegularFieldPathQuery.disjoint(grammar(listOf(f),listOf(listOf(g),listOf(h))),grammar(listOf(g,f),listOf(listOf(g),listOf(h)))))
    }
    @Test fun `empty word is a real shared word`() {
        assertEquals(false,RegularFieldPathQuery.disjoint(grammar(emptyList(),listOf(listOf(g))),grammar(emptyList(),listOf(listOf(h)))))
    }
    @Test fun `omitted grammar alternatives fail the finite compiler certificate`() {
        val full = grammar(listOf(f),listOf(listOf(g),listOf(h)))
        val incomplete = RegularFieldPathQuery.compile(1,full.dropLast(1))!!
        assertFalse(incomplete.validates(full))
    }
    @Test fun `unproved cross-owner epsilon shape returns unknown`() {
        assertNull(RegularFieldPathQuery.compile(2,listOf(RegularFieldPathQuery.Clause(0,emptyList(),1))))
    }
    @Test fun `an unaccounted route outside the chosen writer-reader slice stays unknown`() {
        assertNull(RegularFieldPathQuery.disjoint(grammar(listOf(f),listOf(listOf(g))),grammar(listOf(g),listOf(listOf(g))),completeSlice=false))
    }
    @Test fun `cycles use at most one queue offer per product state`() {
        val a = RegularFieldPathQuery.compile(1,grammar(listOf(f,h),listOf(listOf(g),listOf(h))))!!
        val b = RegularFieldPathQuery.compile(1,grammar(listOf(g,h),listOf(listOf(g),listOf(h))))!!
        val proof = RegularFieldPathQuery.query(a,b)
        assertTrue(proof.empty); assertEquals(proof.states.size,proof.queueOffers)
    }
}

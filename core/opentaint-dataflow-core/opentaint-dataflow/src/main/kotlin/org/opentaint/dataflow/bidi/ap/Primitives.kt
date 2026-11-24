package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.FactTypeChecker

enum class CleanReach { EXACT, BELOW, AT_AND_BELOW }

/** A cleaner targets one program value, optionally for one mark. */
class Cleaner(val base: AccessPathBase, val path: PathNode?, val reach: CleanReach, val mark: TaintMark?) {
    init {
        check(base != AccessPathBase.Zero) { "S11: a cleaner cannot target zero" }
        require(mark != null || reach == CleanReach.AT_AND_BELOW) { "RemoveAll requires the whole position" }
    }
    @JvmField internal val pathArray: IntArray = path?.toIntArray() ?: EMPTY_PATH
}

/** The mark policy of interpreter.md §5.1 (`markPolicyKeeps`): it reads a concrete mark on the value of the base itself
 *  (`elements = 0`) or on the value at `[e]^k` below the base (`elements = k`: the k-th element type). It is NOT a
 *  may-predicate: it reads the mark, not the path, and it can drop a real flow. G6 drop form
 *  (spec/acyclic-convergence-proposal.md §5.1): at a boxed level k a mark that the level does not keep is dropped on the
 *  whole value at `[e]^k`, field leaves included ([dropsValue]). So the policy is prefix-closed (ap.md S5) and monotone
 *  in the field limit. Part II builds a [LevelMarkPolicy] from the static type t; null if no level of t is primitive or
 *  boxed. */
fun interface MarkPolicy {
    fun keeps(mark: TaintMark, elements: Int): Boolean

    /** The level type is boxed: a class that unboxes to a primitive (Integer, Long, Boolean, Character, ...). */
    fun boxedLevel(elements: Int): Boolean = false

    /** The policy drops [mark] on the whole value at the boxed level [elements]: on its leaf and on every leaf below it
     *  (field leaves such as `value`, deeper levels). A boxed value carries only primitive-tracking marks. */
    fun dropsValue(mark: TaintMark, elements: Int): Boolean = boxedLevel(elements) && !keeps(mark, elements)
}

/** The level policy of Part II (JIRTypeFilters.make): level k drops a mark that is not primitive-tracking if the type
 *  at level k is primitive or boxed. [boxed] marks the levels whose type is a class that unboxes to a primitive. */
class LevelMarkPolicy(
    private val primitive: BooleanArray,
    private val boxed: BooleanArray,
    private val primitiveTracking: (TaintMark) -> Boolean,
) : MarkPolicy {
    init { require(primitive.size == boxed.size && boxed.indices.all { !boxed[it] || primitive[it] }) }

    override fun keeps(mark: TaintMark, elements: Int): Boolean =
        !primitive.getOrElse(elements) { false } || primitiveTracking(mark)

    override fun boxedLevel(elements: Int): Boolean = boxed.getOrElse(elements) { false }
}

/** ap.md §4.8: the primitive `filter(b, may)`; `may` is prefix-closed (S5). The base is the key of
 *  StatementSummary.typeFilters (and resultFilters, Part II §23.2). Part II builds `may` with JIRFactTypeChecker (REUSE of
 *  its FactApFilter). `markPolicy` is the policy of the same static type and of its element types, or null (DD9). */
class TypeFilter(val may: FactTypeChecker.FactApFilter, val markPolicy: MarkPolicy? = null) {
    /** interpreter.md §5.1: two filters on one base are a conjunction. */
    fun and(o: TypeFilter): TypeFilter = TypeFilter(AndFilter(may, o.may), when {
        markPolicy == null -> o.markPolicy
        o.markPolicy == null -> markPolicy
        else -> AndPolicy(markPolicy, o.markPolicy)
    })

    /** The conjunction of two policies: a mark is kept if both keep it; a boxed level of either policy is a boxed level,
     *  and either policy can drop a mark on the whole value. */
    private class AndPolicy(val a: MarkPolicy, val b: MarkPolicy) : MarkPolicy {
        override fun keeps(mark: TaintMark, elements: Int): Boolean = a.keeps(mark, elements) && b.keeps(mark, elements)
        override fun boxedLevel(elements: Int): Boolean = a.boxedLevel(elements) || b.boxedLevel(elements)
        override fun dropsValue(mark: TaintMark, elements: Int): Boolean =
            a.dropsValue(mark, elements) || b.dropsValue(mark, elements)
    }

    private class AndFilter(val a: FactTypeChecker.FactApFilter, val b: FactTypeChecker.FactApFilter) : FactTypeChecker.FactApFilter {
        override fun check(accessor: Accessor): FactTypeChecker.FilterResult {
            val x = a.check(accessor)
            val y = b.check(accessor)
            return when {
                x === FactTypeChecker.FilterResult.Reject || y === FactTypeChecker.FilterResult.Reject -> FactTypeChecker.FilterResult.Reject
                x === FactTypeChecker.FilterResult.Accept -> y                                   // Accept and r: r
                y === FactTypeChecker.FilterResult.Accept -> x
                else -> FactTypeChecker.FilterResult.FilterNext(                               // both FilterNext: the conjunction below
                    AndFilter((x as FactTypeChecker.FilterResult.FilterNext).filter, (y as FactTypeChecker.FilterResult.FilterNext).filter))
            }
        }
    }
}


class ConjunctiveEdge(val literals: List<Pattern>, val target: PathFact) {
    init {
        check(literals.size >= 2)
        check(literals.all { it.fact.mark is MarkSlot.Concrete && (it.fact.tail == Tail.EXACT || it.fact.tail == Tail.ANY) })
        check(target.mark is MarkSlot.Concrete && (target.tail == Tail.EXACT || target.tail == Tail.ANY_TAINT))   // W7, I14
        check(target.base != AccessPathBase.Zero)                       // so targetTree(target, layer) is a TaintTree
    }
}

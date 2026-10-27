package org.opentaint.dataflow.bidi.ap

import org.opentaint.dataflow.ap.ifds.AccessPathBase

/** Design review probe. It calls the current scalar AP; it is not a core patch. */
object EmissionRestrictionProbe {
    @JvmStatic fun main(args: Array<String>) {
        val x = AccessPathBase.Argument(0)
        val ret = AccessPathBase.Return
        val t = MarkSlot.Concrete(TaintMark(1))
        val u = MarkSlot.Concrete(TaintMark(2))
        val flow = MarkSlot.STAR
        val excludesT = MarkSlot.Star(MarkSet(intArrayOf(1)))
        val excludesU = MarkSlot.Star(MarkSet(intArrayOf(2)))
        fun p(base: AccessPathBase = x, path: List<Int> = emptyList(),
              tail: Tail = Tail.ANY, mark: MarkSlot = flow,
              e: ExclusionSet = ExclusionSet.Empty) = Pattern(PathFact(base, path, tail, mark), e)
        fun pass(name: String, ok: Boolean) { check(ok) { name }; println("PASS $name") }

        pass("emission T-demand + FLOW-input = none", emit(p(mark = t), p()) == null)
        pass("emission T-demand + FLOW-excluding-U-input = none",
            emit(p(mark = t), p(tail = Tail.STAR, mark = excludesU)) == null)
        pass("emission T-demand + T-input = T", emit(p(mark = t), p(mark = t)) == p(mark = t))
        pass("emission T-demand + U-input = none", emit(p(mark = t), p(mark = u)) == null)
        pass("emission FLOW-demand + T-input = shared STAR/FLOW",
            emit(p(), p(mark = t)) == p(tail = Tail.STAR))
        pass("emission FLOW-demand + FLOW-excluding-T-input = shared STAR/FLOW",
            emit(p(), p(tail = Tail.STAR, mark = excludesT)) == p(tail = Tail.STAR))

        val original = p(tail = Tail.STAR)
        val answer = Conclusion(p(ret, tail = Tail.STAR).fact, ExclusionSet.Empty, false)
        val guide = DemandPattern(p(), p(ret, mark = t))
        pass("restriction T-entry rejects entire FLOW-premise",
            restrict(original, answer, guide.copy(entry = p(mark = t))) == null)
        pass("restriction T-exit keeps FLOW mark and STAR tail",
            restrict(original, answer, guide) == answer)
        pass("restriction T-exit rejects FLOW excluding T",
            restrict(original, answer.copy(fact = answer.fact.copy(mark = excludesT)), guide) == null)
        val otherExcluded = answer.copy(fact = answer.fact.copy(mark = excludesU))
        pass("restriction T-exit keeps FLOW excluding only U",
            restrict(original, otherExcluded, guide) == otherExcluded)
        pass("restriction EXACT T-exit does not cut correlated STAR",
            restrict(original, answer, guide.copy(exit = p(ret, tail = Tail.EXACT, mark = t))) == answer)
        val taintOriginal = p(mark = t)
        val taintAnswer = Conclusion(p(ret, mark = t).fact, ExclusionSet.Empty, true)
        pass("restriction FLOW-entry/exit retains actual T",
            restrict(taintOriginal, taintAnswer, DemandPattern(p(), p(ret))) == taintAnswer)
        pass("restriction U-exit rejects concrete T",
            restrict(taintOriginal, taintAnswer, DemandPattern(p(), p(ret, mark = u))) == null)
        pass("restriction absent exit = none", restrict(original, answer, guide.copy(exit = null)) == null)

        // Current extension bug: E names first accessors at x, not at x.g.
        val f = 10
        val g = 11
        val ancestor = p(tail = Tail.STAR, mark = t, e = ExclusionSet.of(f))
        val deeperDemand = p(path = listOf(g), mark = t)
        val actual = checkNotNull(emit(deeperDemand, ancestor))
        val intended = p(path = listOf(g), tail = Tail.STAR, mark = t)
        val witness = p(path = listOf(g, f), tail = Tail.EXACT, mark = t)
        check(covers(ancestor, witness) && covers(deeperDemand, witness))
        check(actual.exclusion == ExclusionSet.of(f) && !covers(actual, witness))
        check(covers(intended, witness))
        println("CONFIRMED inherited-field-exclusion bug: actual=x.g/STAR/{f}/T intended=x.g/STAR/{}/T; x.g.f is wrongly lost")

        val starDemand = p(tail = Tail.STAR, mark = t)
        val mustActual = p(tail = Tail.ANY_TAINT, mark = t)
        check(runCatching { emit(starDemand, mustActual) }.isFailure)
        println("CONFIRMED STAR-demand adapter gap: current meet rejects MUST-input with STAR-entry; required by preserved STAR demands in later forward runs")
    }
}

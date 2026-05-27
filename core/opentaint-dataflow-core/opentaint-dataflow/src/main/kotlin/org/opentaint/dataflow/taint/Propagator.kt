package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.configuration.CommonTaintAction
import org.opentaint.dataflow.configuration.CommonTaintConfigurationItem
import org.opentaint.util.Maybe
import org.opentaint.util.flatMap
import org.opentaint.util.fmap

interface PassActionEvaluator<T> {
    fun propagateData(rule: CommonTaintConfigurationItem, action: CommonTaintAction, from: PositionAccess, to: PositionAccess): Maybe<List<T>>
    fun propagateTaint(rule: CommonTaintConfigurationItem, action: CommonTaintAction, from: PositionAccess, to: PositionAccess, mark: TaintMarkAccessor): Maybe<List<T>>
}

data class EvaluatedPass(
    val rule: CommonTaintConfigurationItem,
    val action: CommonTaintAction,
    val fact: FinalFactAp,
)

class TaintPassActionEvaluator(
    private val apManager: ApManager,
    private val factTypeChecker: FactTypeChecker,
    private val factReader: FinalFactReader,
    private val positionTypeResolver: PositionTypeResolver,
) : PassActionEvaluator<EvaluatedPass> {
    override fun propagateData(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        from: PositionAccess,
        to: PositionAccess
    ): Maybe<List<EvaluatedPass>> =
        copyAllFacts(from, to).fmap { facts ->
            facts.map { EvaluatedPass(rule, action, it) }
        }

    override fun propagateTaint(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        from: PositionAccess,
        to: PositionAccess,
        mark: TaintMarkAccessor
    ): Maybe<List<EvaluatedPass>> =
        copyFinalFact(from, to, mark).fmap { facts ->
            facts.map { EvaluatedPass(rule, action, it) }
        }

    private fun copyAllFacts(
        fromPosAccess: PositionAccess,
        toPosAccess: PositionAccess,
    ): Maybe<List<FinalFactAp>> {
        if (!factReader.containsPosition(fromPosAccess)) {
            return Maybe.none()
        }

        val fromPositionBaseType = positionTypeResolver.resolve(fromPosAccess)

        val fact = factTypeChecker.filterFactByLocalType(fromPositionBaseType, factReader.factAp)
            ?: return Maybe.some(emptyList())

        val factApDelta = readPosition(
            ap = fact,
            position = fromPosAccess,
            onMismatch = { _, _ ->
                // Position can be filtered out by the type checker
                return Maybe.none()
            },
            matchedNode = { it }
        )

        val toPositionBaseType = positionTypeResolver.resolve(toPosAccess)

        val resultFact = mkAccessPath(toPosAccess, factApDelta, fact.exclusions)
        val wellTypedFact = resultFact.let { factTypeChecker.filterFactByLocalType(toPositionBaseType, it) }
        if (wellTypedFact == null) return Maybe.none()

        return Maybe.some(listOf(factReader.factAp) + wellTypedFact)
    }

    private fun copyFinalFact(
        fromPosAccess: PositionAccess,
        toPosAccess: PositionAccess,
        markRestriction: TaintMarkAccessor,
    ): Maybe<List<FinalFactAp>> {
        if (!factReader.containsPositionWithTaintMark(fromPosAccess, markRestriction)) return Maybe.none()

        val copiedFact = apManager.mkAccessPath(toPosAccess, factReader.factAp.exclusions, markRestriction)

        val toPositionBaseType = positionTypeResolver.resolve(toPosAccess)
        val wellTypedCopy = factTypeChecker.filterFactByLocalType(toPositionBaseType, copiedFact)
            ?: return Maybe.none()

        return Maybe.some(listOf(factReader.factAp) + wellTypedCopy)
    }
}

class TaintPassActionPreconditionEvaluator(
    private val factReader: InitialFactReader,
) : PassActionEvaluator<Pair<CommonTaintAction, InitialFactAp>> {
    override fun propagateData(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        from: PositionAccess,
        to: PositionAccess
    ): Maybe<List<Pair<CommonTaintAction, InitialFactAp>>> {
        return Maybe.from(listOf(to)).flatMap { toVar ->
            copyAllFactsPrecondition(from, toVar).fmap { facts ->
                facts.map { action to it }
            }
        }
    }

    override fun propagateTaint(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        from: PositionAccess,
        to: PositionAccess,
        mark: TaintMarkAccessor
    ): Maybe<List<Pair<CommonTaintAction, InitialFactAp>>> {
        return copyFinalFactPrecondition(from, to, mark).fmap { facts ->
            facts.map { action to it }
        }
    }

    private fun copyAllFactsPrecondition(
        fromPosAccess: PositionAccess,
        toPosAccess: PositionAccess,
    ): Maybe<List<InitialFactAp>> {
        if (!factReader.containsPosition(toPosAccess)) return Maybe.none()

        val fact = factReader.fact
        val factApDelta = readPosition(
            ap = fact,
            position = toPosAccess,
            onMismatch = { _, _ ->
                error("Failed to read $fromPosAccess from $fact")
            },
            matchedNode = { it }
        )
        val preconditionFact = mkAccessPath(fromPosAccess, factApDelta, fact.exclusions)

        return Maybe.some(listOf(preconditionFact))
    }

    private fun copyFinalFactPrecondition(
        fromPosAccess: PositionAccess,
        toPosAccess: PositionAccess,
        mark: TaintMarkAccessor,
    ): Maybe<List<InitialFactAp>> {
        if (!factReader.containsPositionWithTaintMark(toPosAccess, mark)) return Maybe.none()

        val preconditionFact = factReader
            .createInitialFactWithTaintMark(fromPosAccess, mark)
            .replaceExclusions(factReader.fact.exclusions)

        return Maybe.some(listOf(preconditionFact))
    }
}

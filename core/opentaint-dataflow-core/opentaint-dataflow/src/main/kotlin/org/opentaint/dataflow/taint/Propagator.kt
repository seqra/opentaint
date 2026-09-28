package org.opentaint.dataflow.taint

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.ExclusionSet
import org.opentaint.dataflow.ap.ifds.FactTypeChecker
import org.opentaint.dataflow.ap.ifds.TaintMarkAccessor
import org.opentaint.dataflow.ap.ifds.access.ApManager
import org.opentaint.dataflow.ap.ifds.access.FactAp
import org.opentaint.dataflow.ap.ifds.access.FinalFactAp
import org.opentaint.dataflow.ap.ifds.access.InitialFactAp
import org.opentaint.dataflow.ap.ifds.access.ReadableAccessorList
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
    val relevantPositionBase = hashSetOf<AccessPathBase>()

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
        relevantPositionBase += fromPosAccess.base()

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
        relevantPositionBase += fromPosAccess.base()

        if (!factReader.containsPositionWithTaintMark(fromPosAccess, markRestriction)) return Maybe.none()

        val copiedFact = apManager.mkAccessPath(toPosAccess, factReader.factAp.exclusions, markRestriction)

        val toPositionBaseType = positionTypeResolver.resolve(toPosAccess)
        val wellTypedCopy = factTypeChecker.filterFactByLocalType(toPositionBaseType, copiedFact)
            ?: return Maybe.none()

        return Maybe.some(listOf(factReader.factAp) + wellTypedCopy)
    }
}

interface PreconditionFactBuilder<F : FactAp> {
    fun mkFact(position: PositionAccess, positionFact: F, exclusions: ExclusionSet): F
    fun mkFactWithTaintMark(position: PositionAccess, mark: TaintMarkAccessor, exclusions: ExclusionSet): F
    fun filterByPositionType(position: PositionAccess, fact: F): F?
}

class InitialPreconditionFactBuilder(
    private val apManager: ApManager,
) : PreconditionFactBuilder<InitialFactAp> {
    override fun mkFact(position: PositionAccess, positionFact: InitialFactAp, exclusions: ExclusionSet): InitialFactAp =
        mkAccessPath(position, positionFact, exclusions)

    override fun mkFactWithTaintMark(position: PositionAccess, mark: TaintMarkAccessor, exclusions: ExclusionSet): InitialFactAp =
        apManager.mkInitialAccessPath(PositionAccess.Complex(position, mark), ExclusionSet.Universe)
            .replaceExclusions(exclusions)

    override fun filterByPositionType(position: PositionAccess, fact: InitialFactAp): InitialFactAp = fact
}

class FinalPreconditionFactBuilder(
    private val apManager: ApManager,
    private val factTypeChecker: FactTypeChecker,
    private val positionTypeResolver: PositionTypeResolver,
) : PreconditionFactBuilder<FinalFactAp> {
    override fun mkFact(position: PositionAccess, positionFact: FinalFactAp, exclusions: ExclusionSet): FinalFactAp =
        mkAccessPath(position, positionFact, exclusions)

    override fun mkFactWithTaintMark(position: PositionAccess, mark: TaintMarkAccessor, exclusions: ExclusionSet): FinalFactAp =
        apManager.mkAccessPath(position, exclusions, mark)

    override fun filterByPositionType(position: PositionAccess, fact: FinalFactAp): FinalFactAp? =
        factTypeChecker.filterFactByLocalType(positionTypeResolver.resolve(position), fact)
}

class TaintPassActionPreconditionEvaluator<F>(
    private val factReader: FactReader,
    private val fact: F,
    private val factBuilder: PreconditionFactBuilder<F>,
) : PassActionEvaluator<Pair<CommonTaintAction, F>> where F : FactAp, F : ReadableAccessorList<F> {
    override fun propagateData(
        rule: CommonTaintConfigurationItem,
        action: CommonTaintAction,
        from: PositionAccess,
        to: PositionAccess
    ): Maybe<List<Pair<CommonTaintAction, F>>> {
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
    ): Maybe<List<Pair<CommonTaintAction, F>>> {
        return copyFinalFactPrecondition(from, to, mark).fmap { facts ->
            facts.map { action to it }
        }
    }

    private fun copyAllFactsPrecondition(
        fromPosAccess: PositionAccess,
        toPosAccess: PositionAccess,
    ): Maybe<List<F>> {
        if (!factReader.containsPosition(toPosAccess)) return Maybe.none()

        val typedFact = factBuilder.filterByPositionType(toPosAccess, fact)
            ?: return Maybe.some(emptyList())

        val factApDelta = readPositionUtil(
            ap = typedFact,
            apBase = typedFact.base,
            position = toPosAccess,
            onMismatch = { _, _ -> return Maybe.none() },
            matchedNode = { it }
        )

        val preconditionFact = factBuilder.mkFact(fromPosAccess, factApDelta, typedFact.exclusions)
        return preconditionFact.withPositionType(fromPosAccess)
    }

    private fun copyFinalFactPrecondition(
        fromPosAccess: PositionAccess,
        toPosAccess: PositionAccess,
        mark: TaintMarkAccessor,
    ): Maybe<List<F>> {
        if (!factReader.containsPositionWithTaintMark(toPosAccess, mark)) return Maybe.none()

        val preconditionFact = factBuilder.mkFactWithTaintMark(fromPosAccess, mark, fact.exclusions)
        return preconditionFact.withPositionType(fromPosAccess)
    }

    private fun F.withPositionType(position: PositionAccess): Maybe<List<F>> {
        val wellTypedFact = factBuilder.filterByPositionType(position, this) ?: return Maybe.none()
        return Maybe.some(listOf(wellTypedFact))
    }
}

fun TaintPassActionPreconditionEvaluator(
    factReader: InitialFactReader,
): TaintPassActionPreconditionEvaluator<InitialFactAp> =
    TaintPassActionPreconditionEvaluator(factReader, factReader.fact, InitialPreconditionFactBuilder(factReader.apManager))

fun TaintPassActionPreconditionEvaluator(
    factReader: FinalFactReader,
    factTypeChecker: FactTypeChecker,
    positionTypeResolver: PositionTypeResolver,
): TaintPassActionPreconditionEvaluator<FinalFactAp> = TaintPassActionPreconditionEvaluator(
    factReader, factReader.factAp,
    FinalPreconditionFactBuilder(factReader.apManager, factTypeChecker, positionTypeResolver)
)

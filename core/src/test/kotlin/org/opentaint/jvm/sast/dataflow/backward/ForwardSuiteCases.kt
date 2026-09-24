package org.opentaint.jvm.sast.dataflow.backward

import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase.Argument
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedCondition
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRule
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintAssignAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintCleanAction
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.SinkMetaData
import org.opentaint.jvm.sast.dataflow.AnalysisTest.Companion.functionMatcher

data class ForwardCase(
    val suite: String,
    val name: String,
    val entryClass: String,
    val entryMethod: String,
    val config: SerializedTaintConfig,
    val expectedRuleIds: Set<String>,
    val useDefaultConfig: Boolean,
    val unrollFieldsAndElements: Boolean,
) {
    val id: String get() = "$suite/$name"

    val sinks: List<SerializedRule.Sink> get() = config.sink.orEmpty()
}

object ForwardSuiteCases {
    const val JAVA_REACHABILITY = "JavaDataFlowReachabilityTest"
    const val KOTLIN_REACHABILITY = "KotlinDataFlowReachabilityTest"
    const val MULTI_RETURN = "MultiReturnDataFlowTest"
    const val CLEANER_DSL = "CleanerDslAnalysisTest"
    const val CLEANER_CONTROL_FLOW = "CleanerDslControlFlowAnalysisTest"
    const val CLEANER_FIELD_SENSITIVITY = "CleanerFieldSensitivityAnalysisTest"
    const val CLEANER_STAR_DUAL = "CleanerStarDualEvidence"

    private const val SAMPLES = "test.samples"
    private const val TAINTED = "tainted"
    private const val REACH_RULE = "reach"

    val all: List<ForwardCase> by lazy {
        javaReachability() + kotlinReachability() + multiReturn() +
            cleanerDsl() + cleanerControlFlow() + cleanerFieldSensitivity() + cleanerStarDual()
    }

    fun sinkMarks(sink: SerializedRule.Sink): Set<String> = buildSet { sink.condition?.collectMarks(this, positive = true) }

    private fun SerializedCondition.collectMarks(result: MutableSet<String>, positive: Boolean) {
        when (this) {
            is SerializedCondition.And -> allOf.forEach { it.collectMarks(result, positive) }
            is SerializedCondition.Or -> anyOf.forEach { it.collectMarks(result, positive) }
            is SerializedCondition.Not -> not.collectMarks(result, !positive)
            is SerializedCondition.ContainsMark -> if (positive) result += tainted
            else -> Unit
        }
    }

    private fun resultSource(fqn: String, method: String, mark: String) = SerializedRule.Source(
        function = functionMatcher(fqn, method),
        taint = listOf(SerializedTaintAssignAction(kind = mark, pos = PositionBaseWithModifiers.BaseOnly(PositionBase.Result)))
    )

    private fun argumentSink(fqn: String, method: String, ruleId: String, mark: String) = SerializedRule.Sink(
        condition = SerializedCondition.and(
            listOf(SerializedCondition.ContainsMark(mark, PositionBaseWithModifiers.BaseOnly(Argument(0))))
        ),
        function = functionMatcher(fqn, method),
        id = ruleId,
        meta = SinkMetaData(note = "Sink message: $ruleId")
    )

    private fun reachCase(
        suite: String,
        cls: String,
        method: String,
        reachable: Boolean,
        sourceMethod: String = "source",
    ) = ForwardCase(
        suite = suite,
        name = method,
        entryClass = cls,
        entryMethod = method,
        config = SerializedTaintConfig(
            source = listOf(resultSource(cls, sourceMethod, TAINTED)),
            sink = listOf(argumentSink(cls, "sink", REACH_RULE, TAINTED)),
        ),
        expectedRuleIds = if (reachable) setOf(REACH_RULE) else emptySet(),
        useDefaultConfig = true,
        unrollFieldsAndElements = false,
    )

    private fun javaReachability(): List<ForwardCase> {
        val reachable = listOf(
            "SimpleDataFlowSample" to listOf("simpleDataFlow"),
            "FieldFlowSample" to listOf("fieldWriteFlow"),
            "InterproceduralDataFlowSample" to listOf("interproceduralDataFlow"),
            "BranchLoopDataFlowSample" to listOf("branchLoopDataFlow"),
            "CollectionDataFlowSample" to listOf("listAddGetFlow", "mapPutGetFlow", "iteratorFlow"),
            "StringMethodDataFlowSample" to listOf("substringFlow", "toLowerCaseFlow", "trimFlow", "concatFlow", "replaceFlow"),
            "StringBuilderChainDataFlowSample" to listOf("unchained", "chainTaintFirst", "chainedAppend", "namedReturn", "sinkChainResult"),
            "LambdaDataFlowSample" to listOf("lambdaIdentityFlow", "lambdaTransformFlow", "lambdaCaptureFlow", "lambdaPassedToMethodFlow"),
            "OptionalDataFlowSample" to listOf("optionalOfGetFlow", "optionalMapFlow", "optionalOrElseFlow", "optionalFlatMapFlow", "optionalIfPresentFlow"),
            "StreamDataFlowSample" to listOf("streamMapCollectFlow", "streamFilterCollectFlow", "streamReduceFlow", "streamForEachFlow"),
            "AsyncDataFlowSample" to listOf(
                "threadRunnableFlow", "threadLambdaFlow", "callableFutureFlow", "completableFutureSupplyFlow",
                "completableFutureThenApplyFlow", "completableFutureThenAcceptFlow", "executorSubmitRunnableFlow",
            ),
        )
        return reachable.flatMap { (cls, methods) ->
            methods.map { reachCase(JAVA_REACHABILITY, "$SAMPLES.$cls", it, reachable = true) }
        } + listOf(
            reachCase(JAVA_REACHABILITY, "$SAMPLES.FieldFlowSample", "fieldReadKillFlow", reachable = false),
            reachCase(JAVA_REACHABILITY, "$SAMPLES.StreamDataFlowSample", "streamFlatMapFlow", reachable = false),
        )
    }

    private fun kotlinReachability(): List<ForwardCase> {
        val reachable = listOf(
            "KotlinSimpleDataFlowSample" to listOf("simpleDataFlow"),
            "KotlinInterproceduralDataFlowSample" to listOf("interproceduralDataFlow"),
            "KotlinBranchLoopDataFlowSample" to listOf("branchLoopDataFlow"),
            "KotlinCoroutineDataFlowSample" to listOf("runBlockingFlow", "launchFlow", "asyncAwaitFlow"),
            "KotlinCollectionDataFlowSample" to listOf("listAddGetFlow", "mapPutGetFlow", "iteratorFlow"),
            "KotlinStringDataFlowSample" to listOf("substringFlow", "lowercaseFlow", "trimFlow", "plusFlow", "replaceFlow", "stringTemplateFlow"),
            "KotlinLambdaDataFlowSample" to listOf("lambdaIdentityFlow", "lambdaTransformFlow", "lambdaPassedToMethodFlow"),
            "KotlinScopeFunctionDataFlowSample" to listOf("letFlow", "runFlow", "withFlow", "alsoFlow", "applyFlow"),
        )
        val nullSafety = listOf("elvisFlow", "safeCallFlow", "notNullAssertionFlow", "safeCallChainFlow").map {
            reachCase(KOTLIN_REACHABILITY, "$SAMPLES.KotlinNullSafetyDataFlowSample", it, reachable = true, sourceMethod = "nullableSource")
        }
        return reachable.flatMap { (cls, methods) ->
            methods.map { reachCase(KOTLIN_REACHABILITY, "$SAMPLES.$cls", it, reachable = true) }
        } + nullSafety
    }

    private fun multiReturn(): List<ForwardCase> {
        val cls = "$SAMPLES.MultiReturnDataFlowSample"
        val reachable = listOf(
            "allReturnsTaintedFlow", "oneReturnTaintedFlow", "earlyReturnGuardFlow", "nestedMultiReturnFlow",
            "chainedMultiReturnFlow", "loopReturnFlow", "returnOrThrowFlow", "taintArgumentThenReturnFlow",
        )
        val unreachable = listOf("noReturnTaintedFlow", "taintNotReturnedFlow", "taintArgumentThenThrowFlow")
        return reachable.map { reachCase(MULTI_RETURN, cls, it, reachable = true) } +
            unreachable.map { reachCase(MULTI_RETURN, cls, it, reachable = false) }
    }

    private enum class Reach(val methodPart: String) { Plain("Plain"), AnyField("Any") }

    private fun positions(base: PositionBase, reach: Reach): List<PositionBaseWithModifiers> = buildList {
        add(PositionBaseWithModifiers.BaseOnly(base))
        if (reach == Reach.AnyField) {
            add(PositionBaseWithModifiers.WithModifiers(base, listOf(PositionModifier.AnyField)))
        }
    }

    private fun reachSource(cls: String, method: String, reach: Reach, marks: List<String>) = SerializedRule.Source(
        function = functionMatcher(cls, method),
        taint = marks.flatMap { mark ->
            positions(PositionBase.Result, reach).map { SerializedTaintAssignAction(kind = mark, pos = it) }
        }
    )

    private fun reachCleaner(cls: String, method: String, reach: Reach, marks: List<String>, cleansResult: Boolean = false) =
        SerializedRule.Cleaner(
            function = functionMatcher(cls, method),
            cleans = marks.flatMap { mark ->
                buildList {
                    addAll(positions(Argument(0), reach))
                    if (cleansResult) addAll(positions(PositionBase.Result, reach))
                }.map { SerializedTaintCleanAction(taintKind = mark, pos = it) }
            }
        )

    private fun reachSink(cls: String, method: String, reach: Reach, mark: String, ruleId: String) = SerializedRule.Sink(
        condition = SerializedCondition.or(positions(Argument(0), reach).map { SerializedCondition.ContainsMark(mark, it) }),
        function = functionMatcher(cls, method),
        id = ruleId,
        meta = SinkMetaData(note = ruleId),
    )

    private fun reachEntryPoint(cls: String, method: String, arguments: List<Int>, reach: Reach, marks: List<String>) =
        SerializedRule.EntryPoint(
            function = functionMatcher(cls, method),
            taint = arguments.flatMap { argument ->
                marks.flatMap { mark ->
                    positions(Argument(argument), reach).map { SerializedTaintAssignAction(kind = mark, pos = it) }
                }
            },
        )

    private fun cleanerCase(
        suite: String,
        name: String,
        cls: String,
        entryMethod: String,
        config: SerializedTaintConfig,
        expectedRuleIds: Set<String>,
    ) = ForwardCase(suite, name, cls, entryMethod, config, expectedRuleIds, useDefaultConfig = false, unrollFieldsAndElements = true)

    private fun cleanerDsl(): List<ForwardCase> {
        val cls = "$SAMPLES.CleanerDslSample"
        fun marks(count: Int) = (1..count).map { "mark$it" }

        data class MatrixCase(val source: Reach, val cleaner: Reach, val sink: Reach) {
            val sinkMethodPrefix get() = "sink${source.methodPart}${cleaner.methodPart}${sink.methodPart}"
            val id get() = "${source.name}-${cleaner.name}-${sink.name}"
        }

        data class MatrixPoint(val methodSuffix: String, val id: String, val fieldDepth: Int)

        val matrixCases = Reach.entries.flatMap { s -> Reach.entries.flatMap { c -> Reach.entries.map { k -> MatrixCase(s, c, k) } } }
        val matrixPoints = (0..5).map { MatrixPoint("Depth$it", "field-depth$it", it) } +
            (1..5).map { MatrixPoint("StackDepth$it", "stack-depth$it", 1) }

        fun matrixRuleId(case: MatrixCase, point: MatrixPoint, mark: String) = "cleaner-dsl-matrix-${case.id}-${point.id}-$mark"

        fun matrixCase(markCount: Int, sourceReach: Reach, cleanersEnabled: Boolean, name: String): ForwardCase {
            val marks = marks(markCount)
            val entry = "${sourceReach.methodPart.lowercase()}Marks$markCount"
            val cases = matrixCases.filter { it.source == sourceReach }
            val config = SerializedTaintConfig(
                entryPoint = listOf(reachEntryPoint(cls, entry, listOf(0, 1), sourceReach, marks)),
                cleaner = if (cleanersEnabled) {
                    listOf(reachCleaner(cls, "applyPlainClean", Reach.Plain, marks), reachCleaner(cls, "applyAnyClean", Reach.AnyField, marks))
                } else {
                    emptyList()
                },
                sink = cases.flatMap { case ->
                    matrixPoints.flatMap { point ->
                        marks.map { mark -> reachSink(cls, case.sinkMethodPrefix + point.methodSuffix, case.sink, mark, matrixRuleId(case, point, mark)) }
                    }
                },
            )
            val expected = buildSet {
                for (case in cases) {
                    for (point in matrixPoints) {
                        val survives = !cleanersEnabled || (
                            case.source == Reach.AnyField && case.cleaner == Reach.Plain &&
                                (case.sink == Reach.AnyField || point.fieldDepth > 0)
                            )
                        if (survives) marks.mapTo(this) { matrixRuleId(case, point, it) }
                    }
                }
            }
            return cleanerCase(CLEANER_DSL, name, cls, entry, config, expected)
        }

        val matrix = (1..5).flatMap { markCount ->
            Reach.entries.map { reach -> matrixCase(markCount, reach, cleanersEnabled = true, name = "matrix-$markCount-${reach.name}") }
        }
        val noCleaners = matrixCase(5, Reach.AnyField, cleanersEnabled = false, name = "matrix-no-cleaners")

        val selective = (1..5).map { cleanCount ->
            val allMarks = marks(5)
            val entry = "cleanMarks$cleanCount"
            cleanerCase(
                CLEANER_DSL, "selective-clean-$cleanCount", cls, entry,
                SerializedTaintConfig(
                    entryPoint = listOf(reachEntryPoint(cls, entry, listOf(0), Reach.AnyField, allMarks)),
                    cleaner = listOf(reachCleaner(cls, "applyAnyClean", Reach.AnyField, allMarks.take(cleanCount))),
                    sink = allMarks.map { reachSink(cls, "markSelectiveSink", Reach.AnyField, it, "mark-selective-$it") },
                ),
                allMarks.drop(cleanCount).mapTo(hashSetOf()) { "mark-selective-$it" },
            )
        }

        val fieldStore = cleanerCase(
            CLEANER_DSL, "field-store", cls, "fieldStoreExamples",
            SerializedTaintConfig(
                source = listOf(reachSource(cls, "sourcePlain", Reach.Plain, listOf("field-store"))),
                cleaner = listOf(
                    reachCleaner(cls, "cleanPlain", Reach.Plain, listOf("field-store"), cleansResult = true),
                    reachCleaner(cls, "cleanAny", Reach.AnyField, listOf("field-store"), cleansResult = true),
                ),
                sink = listOf(
                    reachSink(cls, "fieldStorePlainSink", Reach.Plain, "field-store", "field-store-plain"),
                    reachSink(cls, "fieldStoreAnySink", Reach.AnyField, "field-store", "field-store-any"),
                    reachSink(cls, "fieldStoreAfterAnyCleanSink", Reach.AnyField, "field-store", "field-store-cleaned"),
                ),
            ),
            setOf("field-store-any"),
        )

        fun helperCases(entry: String, sink: String, mark: String, sourceReach: Reach) = listOf(true, false).map { cleaners ->
            cleanerCase(
                CLEANER_DSL, "$entry-${if (cleaners) "cleaned" else "control"}", cls, entry,
                SerializedTaintConfig(
                    source = listOf(reachSource(cls, "source${sourceReach.methodPart}", sourceReach, listOf(mark))),
                    cleaner = if (cleaners) listOf(reachCleaner(cls, "cleanAny", Reach.AnyField, listOf(mark), cleansResult = true)) else emptyList(),
                    sink = listOf(reachSink(cls, sink, Reach.AnyField, mark, "$mark-sink")),
                ),
                if (cleaners) emptySet() else setOf("$mark-sink"),
            )
        }

        val helpers = helperCases("nestedHelperCleanerExample", "nestedHelperAnySink", "nested-helper", Reach.AnyField) +
            helperCases("helperSourceAndCleanerExample", "helperSourceAnySink", "helper-source", Reach.Plain) +
            helperCases("helperSinkExample", "helperSinkAnySink", "helper-sink", Reach.Plain)

        val conditional = cleanerCase(
            CLEANER_DSL, "conditional", cls, "conditionalExample",
            SerializedTaintConfig(
                source = listOf(
                    reachSource(cls, "sourceA", Reach.AnyField, listOf("a-mark")),
                    reachSource(cls, "sourceX", Reach.AnyField, listOf("x-mark")),
                ),
                cleaner = listOf(
                    reachCleaner(cls, "cleanA", Reach.AnyField, listOf("a-mark"), cleansResult = true),
                    reachCleaner(cls, "cleanX", Reach.AnyField, listOf("x-mark"), cleansResult = true),
                ),
                sink = listOf(
                    reachSink(cls, "sinkA", Reach.AnyField, "a-mark", "conditional-a"),
                    reachSink(cls, "sinkX", Reach.AnyField, "x-mark", "conditional-x"),
                ),
            ),
            setOf("conditional-a", "conditional-x"),
        )

        val returningPlain = cleanerCase(
            CLEANER_DSL, "returning-plain-cleaner", cls, "returningPlainCleaner",
            SerializedTaintConfig(
                entryPoint = listOf(reachEntryPoint(cls, "returningPlainCleaner", listOf(0), Reach.AnyField, listOf("cleaned", "unrelated"))),
                cleaner = listOf(reachCleaner(cls, "cleanPlain", Reach.Plain, listOf("cleaned"), cleansResult = true)),
                sink = listOf(
                    reachSink(cls, "returningPlainSink", Reach.AnyField, "cleaned", "returning-cleaned-any"),
                    reachSink(cls, "returningPlainSink", Reach.Plain, "unrelated", "returning-unrelated-exact"),
                ),
            ),
            setOf("returning-unrelated-exact"),
        )

        val returningAny = cleanerCase(
            CLEANER_DSL, "returning-any-cleaner", cls, "returningAnyCleaner",
            SerializedTaintConfig(
                entryPoint = listOf(reachEntryPoint(cls, "returningAnyCleaner", listOf(0), Reach.AnyField, listOf("unrelated"))),
                cleaner = listOf(reachCleaner(cls, "cleanAny", Reach.AnyField, listOf("absent"), cleansResult = true)),
                sink = listOf(reachSink(cls, "returningAnySink", Reach.Plain, "unrelated", "returning-any-unrelated")),
            ),
            setOf("returning-any-unrelated"),
        )

        fun anyOnlySource(mark: String) = SerializedRule.Source(
            function = functionMatcher(cls, "sourceAnyOnly"),
            taint = listOf(
                SerializedTaintAssignAction(
                    kind = mark,
                    pos = PositionBaseWithModifiers.WithModifiers(PositionBase.Result, listOf(PositionModifier.AnyField)),
                )
            ),
        )

        val anyOnly = cleanerCase(
            CLEANER_DSL, "any-only-source", cls, "anyOnlySourceExample",
            SerializedTaintConfig(
                source = listOf(anyOnlySource("any-only")),
                sink = listOf(
                    reachSink(cls, "anyOnlyRootSink", Reach.AnyField, "any-only", "any-only-root"),
                    reachSink(cls, "anyOnlyChildSink", Reach.Plain, "any-only", "any-only-child"),
                ),
            ),
            setOf("any-only-root", "any-only-child"),
        )

        val recursiveAnyOnly = cleanerCase(
            CLEANER_DSL, "recursive-any-only-source", cls, "recursiveAnyOnlyStoreExample",
            SerializedTaintConfig(
                source = listOf(anyOnlySource("recursive-any-only")),
                sink = listOf(
                    reachSink(cls, "recursiveAnyOnlyRootSink", Reach.AnyField, "recursive-any-only", "recursive-any-only-root"),
                    reachSink(cls, "recursiveAnyOnlyChildSink", Reach.AnyField, "recursive-any-only", "recursive-any-only-child"),
                    reachSink(cls, "recursiveAnyOnlyDepth2Sink", Reach.Plain, "recursive-any-only", "recursive-any-only-depth2"),
                ),
            ),
            setOf("recursive-any-only-root", "recursive-any-only-child", "recursive-any-only-depth2"),
        )

        return matrix + noCleaners + selective + fieldStore + helpers + conditional + returningPlain + returningAny + anyOnly + recursiveAnyOnly
    }

    private fun cleanerControlFlow(): List<ForwardCase> {
        val cls = "$SAMPLES.CleanerDslControlFlowSample"
        val allMarks = (1..5).map { "m$it" }

        val sources = allMarks.mapIndexed { index, mark -> reachSource(cls, "sourceM${index + 1}", Reach.Plain, listOf(mark)) }
        val cleaners = listOf(
            reachCleaner(cls, "cleanM1Plain", Reach.Plain, listOf("m1")),
            reachCleaner(cls, "cleanM1Any", Reach.AnyField, listOf("m1")),
            reachCleaner(cls, "cleanM2Any", Reach.AnyField, listOf("m2")),
            reachCleaner(cls, "cleanM3Any", Reach.AnyField, listOf("m3")),
            reachCleaner(cls, "cleanM4Any", Reach.AnyField, listOf("m4")),
            reachCleaner(cls, "cleanM5Any", Reach.AnyField, listOf("m5")),
            reachCleaner(cls, "cleanM12Any", Reach.AnyField, listOf("m1", "m2")),
            reachCleaner(cls, "cleanM34Any", Reach.AnyField, listOf("m3", "m4")),
            reachCleaner(cls, "cleanAllAny", Reach.AnyField, allMarks),
        )

        fun cp(method: String, vararg surviving: String) = method to surviving.toSet()
        val all = allMarks.toTypedArray()

        fun scenario(entry: String, taintedArguments: List<Int>, vararg checkpoints: Pair<String, Set<String>>) = cleanerCase(
            CLEANER_CONTROL_FLOW, entry, cls, entry,
            SerializedTaintConfig(
                entryPoint = taintedArguments.takeIf { it.isNotEmpty() }
                    ?.let { listOf(reachEntryPoint(cls, entry, it, Reach.AnyField, allMarks)) },
                source = sources,
                cleaner = cleaners,
                sink = checkpoints.flatMap { (method, _) -> allMarks.map { reachSink(cls, method, Reach.AnyField, it, "$method-$it") } },
            ),
            checkpoints.flatMapTo(hashSetOf()) { (method, surviving) -> surviving.map { "$method-$it" } },
        )

        return listOf(
            scenario(
                "sequentialMarks", emptyList(),
                cp("sequenceStartSink", "m1", "m2", "m3"),
                cp("sequenceAfterM1Sink", "m2", "m3"),
                cp("sequenceAfterM2Sink", "m3"),
                cp("sequenceAfterM4SourceSink", "m3", "m4"),
                cp("sequenceAfterM3Sink", "m4"),
                cp("sequenceAllCleanSink"),
                cp("sequenceNestedAfterPlainSink", "m1"),
                cp("sequenceNestedAfterAnySink"),
            ),
            scenario(
                "divergentBranches", listOf(0),
                cp("divergentJoinSink", *all),
                cp("divergentAfterM5Sink", "m1", "m2", "m3", "m4"),
                cp("convergentJoinSink", "m3", "m4"),
            ),
            scenario(
                "earlyReturnSummaries", listOf(0, 1),
                cp("maybeCleanReturnSink", *all),
                cp("alwaysCleanReturnSink", "m3", "m4", "m5"),
            ),
            scenario(
                "aliasesAndReassignment", listOf(0),
                cp("aliasOriginalSink", *all),
                cp("reassignedOldSink", "m3", "m4", "m5"),
                cp("reassignedNewSink", "m1"),
                cp("unsanitizedOriginalSink", *all),
                cp("independentReassignmentSink", "m1"),
            ),
            scenario(
                "deepCleanerPipeline", listOf(0, 1),
                cp("deepPipelineCleanedSink"),
                cp("deepPipelineControlSink", *all),
            ),
            scenario("doWhileCleaner", listOf(0), cp("doWhileSink", "m2", "m3", "m4", "m5")),
            scenario("zeroOrMoreCleaner", listOf(0), cp("zeroOrMoreSink", *all)),
            scenario(
                "independentBranchValues", listOf(0, 1),
                cp("independentLeftJoinSink", *all),
                cp("independentRightJoinSink", *all),
                cp("independentLeftCleanedSink"),
                cp("independentRightUnchangedSink", *all),
            ),
            scenario(
                "cleanThenRetain", emptyList(),
                cp("cleanBeforeNewSourceSink"),
                cp("newSourceAfterCleanSink", "m2"),
                cp("newSourceCleanedSink"),
            ),
        )
    }

    private fun cleanerFieldSensitivity(): List<ForwardCase> {
        val cls = "$SAMPLES.DeepCleanSummarySample"
        val box = "$cls\$Box"
        val node = "$cls\$Node"
        val leaf = "$cls\$Leaf"
        val boxF = PositionModifier.Field(box, "f", "java.lang.String")
        val nodeF = PositionModifier.Field(node, "f", leaf)
        val leafK = PositionModifier.Field(leaf, "k", "java.lang.String")
        val ruleId = "cleaner-field-sensitivity-rule"

        fun source(entry: String, vararg positions: PositionBaseWithModifiers) = SerializedRule.EntryPoint(
            function = functionMatcher(cls, entry),
            taint = positions.map { SerializedTaintAssignAction(kind = TAINTED, pos = it) }
        )

        fun cleaner(method: String, vararg positions: PositionBaseWithModifiers) = SerializedRule.Cleaner(
            function = functionMatcher(cls, method),
            cleans = positions.map { SerializedTaintCleanAction(taintKind = TAINTED, pos = it) }
        )

        val baseOnly = PositionBaseWithModifiers.BaseOnly(Argument(0))
        fun withModifiers(vararg modifiers: PositionModifier) = PositionBaseWithModifiers.WithModifiers(Argument(0), modifiers.toList())
        val anyField = withModifiers(PositionModifier.AnyField)
        fun starred(method: String) = cleaner(method, baseOnly, anyField)

        fun case(name: String, entry: String, sinkMethod: String, source: SerializedRule.EntryPoint, cleaner: SerializedRule.Cleaner?, reachable: Boolean) =
            cleanerCase(
                CLEANER_FIELD_SENSITIVITY, name, cls, entry,
                SerializedTaintConfig(
                    entryPoint = listOf(source),
                    cleaner = listOfNotNull(cleaner),
                    sink = listOf(argumentSink(cls, sinkMethod, ruleId, TAINTED)),
                ),
                if (reachable) setOf(ruleId) else emptySet(),
            )

        return listOf(
            case("concrete-base-unsanitized", "boxUncleanedFlow", "sinkBox", source("boxUncleanedFlow", baseOnly), cleaner("clean", baseOnly), true),
            case("concrete-base-sanitized", "boxCleanedFlow", "sinkBox", source("boxCleanedFlow", baseOnly), cleaner("clean", baseOnly), false),
            case("starred-depth1-unsanitized", "boxUncleanedFlow", "sinkBox", source("boxUncleanedFlow", baseOnly, anyField), starred("clean"), true),
            case("starred-depth1-sanitized", "boxCleanedFlow", "sinkBox", source("boxCleanedFlow", baseOnly, anyField), starred("clean"), false),
            case("concrete-field-unsanitized", "uncleanedFlow", "sink", source("uncleanedFlow", withModifiers(boxF)), cleaner("clean", withModifiers(boxF)), true),
            case("concrete-field-sanitized", "cleanedFlow", "sink", source("cleanedFlow", withModifiers(boxF)), cleaner("clean", withModifiers(boxF)), false),
            case("starred-depth2-unsanitized", "uncleanedFlow", "sink", source("uncleanedFlow", withModifiers(boxF)), starred("clean"), true),
            case("starred-depth2-sanitized", "cleanedFlow", "sink", source("cleanedFlow", withModifiers(boxF)), starred("clean"), false),
            case("concrete-two-level-unsanitized", "nodeUncleanedFlow", "sink", source("nodeUncleanedFlow", anyField), cleaner("cleanNode", withModifiers(nodeF, leafK)), true),
            case("concrete-two-level-sanitized", "nodeCleanedFlow", "sink", source("nodeCleanedFlow", anyField), cleaner("cleanNode", withModifiers(nodeF, leafK)), false),
            case("starred-depth3-unsanitized", "nodeUncleanedFlow", "sink", source("nodeUncleanedFlow", anyField), starred("cleanNode"), true),
            case("starred-depth3-sanitized", "nodeCleanedFlow", "sink", source("nodeCleanedFlow", anyField), starred("cleanNode"), false),
            case("non-vacuity-base-depth1", "boxCleanedFlow", "sinkBox", source("boxCleanedFlow", baseOnly), null, true),
            case("non-vacuity-whole-object-depth1", "boxCleanedFlow", "sinkBox", source("boxCleanedFlow", baseOnly, anyField), null, true),
            case("non-vacuity-field-depth2", "cleanedFlow", "sink", source("cleanedFlow", withModifiers(boxF)), null, true),
            case("non-vacuity-any-field-depth3", "nodeCleanedFlow", "sink", source("nodeCleanedFlow", anyField), null, true),
        )
    }

    private fun cleanerStarDual(): List<ForwardCase> {
        val cls = "$SAMPLES.CleanerStarDualSample"
        val mark = "star"
        val cleaner = reachCleaner(cls, "applyPlainClean", Reach.Plain, listOf(mark))

        fun entryCase(entry: String, reachable: Boolean) = cleanerCase(
            CLEANER_STAR_DUAL, entry, cls, entry,
            SerializedTaintConfig(
                entryPoint = listOf(reachEntryPoint(cls, entry, listOf(0), Reach.AnyField, listOf(mark))),
                cleaner = listOf(cleaner),
                sink = listOf(reachSink(cls, "fieldSink", Reach.Plain, mark, "field-sink")),
            ),
            if (reachable) setOf("field-sink") else emptySet(),
        )

        return listOf(
            entryCase("inlineCleanerThenFieldSink", reachable = false),
            entryCase("calleeCleanerThenFieldSink", reachable = true),
            cleanerCase(
                CLEANER_STAR_DUAL, "nestedStoreThenCleanerThenAnySink", cls, "nestedStoreThenCleanerThenAnySink",
                SerializedTaintConfig(
                    source = listOf(reachSource(cls, "source", Reach.Plain, listOf(mark))),
                    cleaner = listOf(cleaner),
                    sink = listOf(reachSink(cls, "anySink", Reach.AnyField, mark, "any-sink")),
                ),
                setOf("any-sink"),
            ),
        )
    }
}

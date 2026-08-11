package org.opentaint.jvm.sast.dataflow

import kotlinx.coroutines.runBlocking
import org.opentaint.common.sast.dataflow.TaintAnalyzer
import org.opentaint.common.sast.dataflow.TaintAnalyzerOptions
import org.opentaint.dataflow.ap.ifds.taint.ExternalMethodTracker
import org.opentaint.dataflow.ifds.UnitType
import org.opentaint.dataflow.ifds.UnknownUnit
import org.opentaint.dataflow.jvm.ap.ifds.JIRLocalAliasAnalysis
import org.opentaint.dataflow.jvm.ap.ifds.JIRSafeApplicationGraph
import org.opentaint.dataflow.jvm.ap.ifds.JIRSummarySerializationContext
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature
import org.opentaint.dataflow.jvm.ap.ifds.LambdaAnonymousClassFeature.JIRLambdaMethod
import org.opentaint.dataflow.jvm.ap.ifds.analysis.JIRAnalysisManager
import org.opentaint.dataflow.jvm.ap.ifds.taint.TaintRulesProvider
import org.opentaint.dataflow.jvm.ifds.JIRUnitResolver
import org.opentaint.dataflow.jvm.ifds.PackageUnit
import org.opentaint.ir.api.jvm.JIRClassOrInterface
import org.opentaint.ir.api.jvm.JIRClasspath
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.RegisteredLocation
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.ir.api.jvm.ext.packageName
import org.opentaint.dataflow.ap.ifds.Accessor
import org.opentaint.dataflow.ap.ifds.ClassStaticAccessor
import org.opentaint.dataflow.ap.ifds.FieldAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.configuration.jvm.serialized.SerializedRuleUniverse
import org.opentaint.ir.impl.features.usagesExt
import org.objectweb.asm.Opcodes
import org.objectweb.asm.tree.FieldInsnNode
import org.objectweb.asm.tree.InvokeDynamicInsnNode
import org.opentaint.jvm.graph.JApplicationGraphImpl
import org.opentaint.jvm.sast.dataflow.DataFlowApproximationLoader.isApproximation
import org.opentaint.util.analysis.ApplicationGraph

private val logger = mu.KotlinLogging.logger {}

class JIRTaintAnalyzer(
    val cp: JIRClasspath,
    val taintConfiguration: TaintRulesProvider,
    val projectClasses: ClassLocationChecker,
    options: TaintAnalyzerOptions,
    val jirOptions: JIRAnalysisOptions = JIRAnalysisOptions(),
    val analysisUnit: JIRUnitResolver = PackageUnitResolver(projectClasses),
    externalMethodTracker: ExternalMethodTracker? = null,
): TaintAnalyzer<JIRMethod, JIRInst>(options, externalMethodTracker) {
    override fun analysisGraph(): ApplicationGraph<JIRMethod, JIRInst> {
        val usages = runBlocking { cp.usagesExt() }
        val mainGraph = JApplicationGraphImpl(cp, usages)
        val tryBoundaryExceptionsGraph = JTryBoundaryExceptionsApplicationGraph(mainGraph)
        return JIRSafeApplicationGraph(tryBoundaryExceptionsGraph)
    }

    data class JIRAnalysisOptions(
        val disableDefaultGetModel: Boolean = false,
    )

    private val analysisParams get() = JIRAnalysisManager.Params(
        disableDefaultGetModel = jirOptions.disableDefaultGetModel,
        aliasAnalysisParams = JIRLocalAliasAnalysis.Params(
            aliasAnalysisInterProcCallDepth = options.experimentalAAInterProcCallDepth
        )
    )

    private val taintConfig: TaintRulesProvider by lazy {
        StringConcatRuleProvider(taintConfiguration)
    }

    override fun analysisManager() =
        JIRAnalysisManager(cp, refManager, taintConfig, externalMethodTracker, analysisParams)

    override fun unitResolver() = analysisUnit

    override fun summarySerializationContext() = JIRSummarySerializationContext(cp)

    /**
     * The statically enumerable part of the accessor universe:
     *
     * - a class-static accessor for every class name in every registered location, and
     * - a field accessor for every declared field of every project class and of every class
     *   the loaded rules reference by name (the classes taint actually flows through).
     *
     * Lambda classes and their capture fields exist only after synthesis, so the
     * instruction lists of project methods that can synthesize one (bytecode contains an
     * invokedynamic) are forced here, and the resulting classes are enumerated too.
     */
    override fun platformAccessorUniverse(): Sequence<Accessor> {
        val accessors = mutableListOf<Accessor>()

        // Class names come from BOTH the persisted sources and the location's own listing:
        // the persistence covers locations whose jar facade cannot list classes, and the
        // facade covers dependency jars that are resolved lazily and never fully persisted.
        // Anything missed here is interned in analysis-thread arrival order and would
        // reintroduce the fingerprint drift.
        for (location in cp.registeredLocations) {
            for (source in cp.db.persistence.findClassSources(cp.db, location)) {
                accessors += ClassStaticAccessor(source.className)
            }
            for (name in location.jIRLocation?.classNames.orEmpty()) {
                accessors += ClassStaticAccessor(name)
            }
        }

        // Every failure below narrows the seed, and a seed hole is exactly what
        // reintroduces the drift -- so failures are counted and surfaced, never swallowed.
        val classesNotResolved = java.util.concurrent.atomic.AtomicInteger()
        val fieldEnumerationFailures = java.util.concurrent.atomic.AtomicInteger()
        val lambdaForceFailures = java.util.concurrent.atomic.AtomicInteger()

        val fieldClasses = mutableListOf<String>()
        fieldClasses += projectClasses.projectClassNames()
        fieldClasses += SerializedRuleUniverse.matcherClassNames()
        fieldClasses += SerializedRuleUniverse.staticPositionClassNames()

        // Class parsing dominates the cost of this enumeration and every class is
        // independent, so it runs on the common pool; the results are sorted before
        // interning, which makes the collection order irrelevant.
        val parsed = fieldClasses.distinct().parallelStream().map { name ->
            val cls = runCatching { cp.findClassOrNull(name) }.getOrNull()
            if (cls == null) {
                classesNotResolved.incrementAndGet()
                return@map null
            }
            val fields = runCatching {
                cls.declaredFields.map { FieldAccessor(cls.name, it.name, it.type.typeName) }
            }.getOrElse {
                fieldEnumerationFailures.incrementAndGet()
                emptyList()
            }
            Triple(cls, projectClasses.isProjectClass(cls), fields)
        }.toList().filterNotNull()

        parsed.forEach { (_, _, fields) -> accessors += fields }

        // Lambda classes are synthesized as a side effect of building a method's instruction
        // list, and only project methods are analyzed, so forcing project instruction lists
        // materializes the whole lambda universe deterministically. Only methods whose
        // bytecode actually contains an invokedynamic can synthesize one, so everything else
        // is skipped -- the cheap ASM scan keeps this pass out of the analysis wall clock.
        // The same bytecode pass collects every class whose static fields project code
        // reads or writes: their <static> accessors are interned mid-analysis when a fact
        // first reaches them, and lazily-resolved dependency locations do not reliably
        // list such classes -- the last observed enumeration hole (a dozen
        // pdfbox/spring/bouncycastle statics interned in arrival order).
        val staticOwners = java.util.concurrent.ConcurrentHashMap.newKeySet<String>()
        parsed.filter { it.second }.parallelStream().forEach { (cls, _, _) ->
            for (method in cls.declaredMethods) {
                runCatching {
                    val hasIndy = method.withAsmNode { node ->
                        var indy = false
                        for (insn in node.instructions) {
                            if (insn is InvokeDynamicInsnNode) indy = true
                            if (insn is FieldInsnNode &&
                                (insn.opcode == Opcodes.GETSTATIC || insn.opcode == Opcodes.PUTSTATIC)
                            ) {
                                staticOwners += insn.owner.replace('/', '.')
                            }
                        }
                        indy
                    }
                    if (hasIndy) method.instList
                }.onFailure { lambdaForceFailures.incrementAndGet() }
            }
        }
        staticOwners.mapTo(accessors) { ClassStaticAccessor(it) }
        cp.features.orEmpty().filterIsInstance<LambdaAnonymousClassFeature>().forEach { feature ->
            for (lambdaClass in feature.allLambdaClasses()) {
                accessors += TypeInfoAccessor(lambdaClass.name)
                accessors += ClassStaticAccessor(lambdaClass.name)
                for (field in lambdaClass.declaredFields) {
                    accessors += FieldAccessor(lambdaClass.name, field.name, field.type.typeName)
                }
            }
        }

        val failures = classesNotResolved.get() + fieldEnumerationFailures.get() + lambdaForceFailures.get()
        if (failures > 0) {
            logger.warn {
                "accessor universe enumeration is incomplete: " +
                    "${classesNotResolved.get()} classes unresolved, " +
                    "${fieldEnumerationFailures.get()} field enumerations failed, " +
                    "${lambdaForceFailures.get()} lambda-synthesis forcings failed; " +
                    "accessors of the affected classes are interned in arrival order and " +
                    "SARIF trace fingerprints may vary between runs (diff -Dprobe.internerdump to localize)"
            }
        }

        return accessors.asSequence()
    }

    override fun coverageReportTool() = object : AnalyzerCoverageReportTool<JIRMethod, JIRClassOrInterface> {
        override fun includeInReport(method: JIRMethod): Boolean {
            val cls = method.enclosingClass
            if (cls is LambdaAnonymousClassFeature.JIRLambdaClass) return false
            return projectClasses.isProjectClass(cls)
        }

        override fun methodInstructionCount(method: JIRMethod): Int = method.instList.size
        override fun groupingUnit(method: JIRMethod): JIRClassOrInterface = method.enclosingClass
        override fun printUnit(key: JIRClassOrInterface): String = key.name
        override fun unitMethods(unit: JIRClassOrInterface): List<JIRMethod> = unit.declaredMethods
    }

    companion object {
        class PackageUnitResolver(private val projectLocations: ClassLocationChecker) : JIRUnitResolver {
            override fun resolve(method: JIRMethod): UnitType {
                if (!projectLocations.isProjectClass(method.enclosingClass) && !isApproximation(method) && method !is JIRLambdaMethod) {
                    return UnknownUnit
                }

                return PackageUnit(method.enclosingClass.packageName)
            }

            override fun locationIsUnknown(loc: RegisteredLocation): Boolean =
                !projectLocations.isProjectLocation(loc)
        }
    }
}
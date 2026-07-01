package org.opentaint.jvm.sast.project

import io.github.detekt.sarif4k.Location
import io.github.detekt.sarif4k.LogicalLocation
import io.github.detekt.sarif4k.Message
import io.github.detekt.sarif4k.PropertyBag
import io.github.detekt.sarif4k.Result
import org.opentaint.common.sast.sarif.TracePathNode
import org.opentaint.dataflow.ap.ifds.taint.TaintSinkTracker
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTrace
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedInterProceduralTraceEntry
import org.opentaint.dataflow.ap.ifds.trace.path.ResolvedNodeTrace
import org.opentaint.dataflow.ap.ifds.trace.path.TracePathGenerationResult
import org.opentaint.ir.api.common.CommonMethod
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRInst
import org.opentaint.jvm.sast.JIRSourceFileResolver
import org.opentaint.jvm.sast.ast.AstSpanResolverProvider

abstract class SarifWebInfoAnnotator(
    val sourceFileResolver: JIRSourceFileResolver,
    val spanResolver: AstSpanResolverProvider,
) {
    interface ControllerParams

    data class ControllerPathInfo(
        val path: String,
        val method: String?,
    )

    data class ControllerInfo(
        val controller: JIRMethod,
        val pathInfo: List<ControllerPathInfo>,
        val params: ControllerParams?,
    )

    abstract fun JIRMethod.isController(): Boolean

    abstract fun createControllerInfo(
        controllers: List<JIRMethod>,
        vulnerability: TaintSinkTracker.TaintVulnerability,
        trace: TracePathGenerationResult,
        tracePaths: List<List<TracePathNode>>,
    ): List<ControllerInfo>

    abstract fun ControllerInfo.paramsToProperties(): PropertyBag?

    fun annotateSarif(
        result: Result,
        vulnerability: TaintSinkTracker.TaintVulnerability,
        trace: TracePathGenerationResult,
        tracePaths: List<List<TracePathNode>>,
        generateStatementLocation: (JIRInst) -> Location?
    ): Result {
        val relevantMethods = vulnRelevantMethods(vulnerability, trace)
        val relevantControllers = relevantMethods
            .filterIsInstance<JIRMethod>()
            .filter { it.isController() }

        if (relevantControllers.isEmpty()) return result

        val relevantControllerInfo = createControllerInfo(relevantControllers, vulnerability, trace, tracePaths)

        val relatedLocations = result.relatedLocations.orEmpty().toMutableList()
        for (controllerInfo in relevantControllerInfo) {
            val controller = controllerInfo.controller
            val firstInst = controller.instList.firstOrNull() ?: continue
            val paths = controllerInfo.pathInfo
            val propertyBag = controllerInfo.paramsToProperties()

            val logicalLoc = paths.mapIndexed { i, path ->
                LogicalLocation(
                    fullyQualifiedName = "${path.method?.let { "$it " } ?: ""}${path.path}",
                    index = i.toLong(),
                    name = "${controller.enclosingClass.name}#${controller.name}",
                    kind = "function",
                    properties = propertyBag
                )
            }

            val loc = generateStatementLocation(firstInst)
                ?: continue

            relatedLocations += Location(
                logicalLocations = logicalLoc,
                physicalLocation = loc.physicalLocation,
                message = Message(text = "Related Spring controller")
            )
        }
        return result.copy(relatedLocations = relatedLocations)
    }

    private fun vulnRelevantMethods(
        vulnerability: TaintSinkTracker.TaintVulnerability,
        trace: TracePathGenerationResult,
    ): Set<CommonMethod> {
        val methods = hashSetOf<CommonMethod>()
        methods.add(vulnerability.statement.location.method)

        if (trace !is TracePathGenerationResult.Path) return methods

        trace.path.forEach {
            collectRelevantMethods(it, methods)
        }

        return methods
    }

    private fun collectRelevantMethods(trace: ResolvedNodeTrace, methods: MutableSet<CommonMethod>) {
        trace.root2Source.forEach { collectRelevantMethods(it, methods) }
        trace.root2SinkNoRoot.forEach { collectRelevantMethods(it, methods) }
    }

    private fun collectRelevantMethods(trace: ResolvedInterProceduralTrace, methods: MutableSet<CommonMethod>) {
        methods += trace.method.method
        trace.entries
            .filterIsInstance<ResolvedInterProceduralTraceEntry.InnerCall>()
            .forEach { collectRelevantMethods(it.innerTrace, methods) }
    }
}

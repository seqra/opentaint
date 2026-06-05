package org.opentaint.dataflow.call

import org.opentaint.dataflow.ap.ifds.AccessPathBase
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer
import org.opentaint.dataflow.ap.ifds.MethodAnalyzer.MethodCallHandler
import org.opentaint.dataflow.ap.ifds.TypeInfoAccessor
import org.opentaint.dataflow.ap.ifds.TypeInfoGroupAccessor

inline fun tryExtractCallTypeInfo(
    handler: MethodCallHandler,
    analyzer: MethodAnalyzer,
    isValidCallPosition: (AccessPathBase) -> Boolean,
    handleTypeInfo: (TypeInfoAccessor) -> Unit
) {
    val (start, fact) = when (handler) {
        is MethodCallHandler.ZeroToZeroHandler,
        is MethodCallHandler.NDFactToFactHandler -> return

        is MethodCallHandler.FactToFactHandler -> {
            handler.startFactBase to handler.currentEdge.factAp
        }

        is MethodCallHandler.ZeroToFactHandler -> {
            handler.startFactBase to handler.currentEdge.factAp
        }
    }

    if (!isValidCallPosition(start)) return

    val typeInfoGroup = fact.readAccessor(TypeInfoGroupAccessor)
    if (typeInfoGroup == null) {
        if (handler is MethodCallHandler.FactToFactHandler) {
            val edge = handler.currentEdge
            val refinedInitial = edge.initialFactAp.exclude(TypeInfoGroupAccessor)
            analyzer.triggerSideEffectRequirement(refinedInitial)
        }
        return
    }

    val typeInfos = typeInfoGroup.getStartAccessors().filterIsInstance<TypeInfoAccessor>()
    typeInfos.forEach { typeInfo ->
        handleTypeInfo(typeInfo)
    }
}

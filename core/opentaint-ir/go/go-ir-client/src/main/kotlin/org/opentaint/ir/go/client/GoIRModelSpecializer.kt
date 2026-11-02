package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRGlobalReference
import org.opentaint.ir.go.api.GoIRPackage
import org.opentaint.ir.go.api.GoIRParameter
import org.opentaint.ir.go.api.GoIRFreeVar
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.api.GoIRTypeParamDecl
import org.opentaint.ir.go.api.GoIrFunctionReference
import org.opentaint.ir.go.impl.GoIRFunctionImpl
import org.opentaint.ir.go.type.*
import java.util.IdentityHashMap

/** Substitutes concrete type arguments and closure lookups while reading a generic model body. */
internal class GoIRModelSpecializer(
    private val program: GoIRProgram,
    private val pkg: GoIRPackage,
    private val model: GoIRBodyContext,
    private val symbol: (String) -> String,
) {
    /** Returns the specialized root followed by its specialized anonymous functions. */
    fun specialize(modelRoot: GoIRFunction, target: GoIRFunction): List<GoIRFunction> {
        require(modelRoot.bodyAvailable) { "Go model function ${modelRoot.fullName} has no body" }
        require(modelRoot.typeParams.size == target.typeArgs.size) {
            "Go generic instance ${target.fullName} has ${target.typeArgs.size} type arguments, " +
                "want ${modelRoot.typeParams.size}"
        }
        val typeArguments = modelRoot.typeParams.associate { parameter ->
            parameter.index to target.typeArgs[parameter.index]
        }
        val specializer = TypeSpecializer(typeArguments)
        fun specializeType(type: GoIRType) = specializer(model.type(type))
        val sourceFunctions = collectAnonymousFunctions(modelRoot)
        val suffix = target.name.removePrefix(modelRoot.name).ifEmpty {
            "#opentaint-model-${target.fullName.hashCode().toUInt()}"
        }
        val functionMap = IdentityHashMap<GoIRFunction, GoIRFunctionImpl>()
        val anonymousRefs = IdentityHashMap<GoIRFunction, MutableList<GoIrFunctionReference>>()

        fun reference(function: GoIRFunction): GoIrFunctionReference =
            GoIrFunctionReference(pkg.importPath, function.name, function.signature)
                .also { it.program = program }

        val rootRefs = mutableListOf<GoIrFunctionReference>()
        val root = modelFunction(
            original = target,
            name = target.name,
            fullName = target.fullName,
            pkg = pkg,
            signature = target.signature,
            params = target.params,
            freeVars = target.freeVars,
            position = modelRoot.position,
            isMethod = target.isMethod,
            isPointerReceiver = target.isPointerReceiver,
            isExported = target.isExported,
            syntheticKind = modelRoot.syntheticKind,
            hasBody = true,
            parent = target.parent,
            anonymousFunctions = rootRefs,
            typeParams = target.typeParams,
            originFullName = target.originFullName,
            typeArgs = target.typeArgs,
        )
        functionMap[modelRoot] = root
        anonymousRefs[modelRoot] = rootRefs

        sourceFunctions.forEach { source ->
            val refs = mutableListOf<GoIrFunctionReference>()
            val parent = source.parent?.function?.let(functionMap::get)
                ?: error("Go model anonymous function ${source.fullName} has no copied parent")
            val copied = modelFunction(
                original = null,
                name = source.name + suffix,
                fullName = symbol(source.fullName) + suffix,
                pkg = pkg,
                signature = specializeType(source.signature) as GoIRFuncType,
                params = source.params.map { GoIRParameter(it.name, specializeType(it.type), it.index) },
                freeVars = source.freeVars.map { GoIRFreeVar(it.name, specializeType(it.type), it.index) },
                position = source.position,
                isMethod = source.isMethod,
                isPointerReceiver = source.isPointerReceiver,
                isExported = source.isExported,
                syntheticKind = source.syntheticKind,
                hasBody = true,
                parent = reference(parent),
                anonymousFunctions = refs,
                typeParams = source.typeParams.map {
                    GoIRTypeParamDecl(it.name, it.index, specializeType(it.constraint))
                },
                originFullName = null,
                typeArgs = emptyList(),
            )
            functionMap[source] = copied
            anonymousRefs[source] = refs
        }

        (listOf(modelRoot) + sourceFunctions).forEach { source ->
            val refs = anonymousRefs.getValue(source)
            refs += source.anonymousFunctions.map { child ->
                functionMap[child.function]?.let(::reference) ?: model.function(child)
            }
        }

        val context = object : GoIRBodyContext() {
            override fun type(type: GoIRType) = specializeType(type)
            override fun function(reference: GoIrFunctionReference): GoIrFunctionReference =
                reference.program.lookup.function(reference)?.let(functionMap::get)?.let(::reference)
                    ?: model.function(reference)
            override fun global(reference: GoIRGlobalReference) = model.global(reference)
            override fun fieldIndex(type: GoIRType, index: Int, name: String) =
                model.fieldIndex(type, index, name)
        }
        (listOf(modelRoot) + sourceFunctions).forEach { source ->
            functionMap.getValue(source).setBodyReader { owner, _ ->
                (source as GoIRFunctionImpl).readBody(owner, context)
                    ?: error("Go model ${source.fullName} has no body")
            }
        }
        return listOf(root) + sourceFunctions.map(functionMap::getValue)
    }

    private fun collectAnonymousFunctions(root: GoIRFunction): List<GoIRFunction> {
        val result = mutableListOf<GoIRFunction>()
        val pending = ArrayDeque(root.anonymousFunctions.map { it.function })
        while (pending.isNotEmpty()) {
            val function = pending.removeFirst()
            if (result.any { it === function }) continue
            result += function
            pending += function.anonymousFunctions.map { it.function }
        }
        return result
    }

}

private class TypeSpecializer(
    private val arguments: Map<Int, GoIRType>,
) : (GoIRType) -> GoIRType {
    override fun invoke(type: GoIRType): GoIRType {
        val result = when (type) {
            is GoIRTypeParamType -> arguments[type.paramIndex] ?: type
            is GoIRTypeParamRef -> arguments[type.paramIndex] ?: type
            is GoIRPointerType -> GoIRPointerType(invoke(type.elem))
            is GoIRArrayType -> GoIRArrayType(invoke(type.elem), type.length)
            is GoIRSliceType -> GoIRSliceType(invoke(type.elem))
            is GoIRMapType -> GoIRMapType(invoke(type.key), invoke(type.value))
            is GoIRChanType -> GoIRChanType(invoke(type.elem), type.direction)
            is GoIRStructType -> GoIRStructType(
                type.fields.map { GoIRStructField(it.name, invoke(it.type), it.isEmbedded, it.tag) },
                type.structTypeRef,
            )
            is GoIRNamedTypeRef -> GoIRNamedTypeRef(type.typeRef, type.typeArgs.map(::invoke))
            is GoIRNamedInterfaceType -> GoIRNamedInterfaceType(
                type.methods.map { GoIRInterfaceMethodSig(it.name, invoke(it.signature) as GoIRFuncType) },
                type.embeds.map(::invoke),
                type.interfaceTypeRef,
            )
            is GoIRAnonymousInterfaceType -> GoIRAnonymousInterfaceType(
                type.id,
                type.methods.map { GoIRInterfaceMethodSig(it.name, invoke(it.signature) as GoIRFuncType) },
                type.embeds.map(::invoke),
            )
            is GoIRFuncType -> GoIRFuncType(
                type.params.map(::invoke),
                type.results.map(::invoke),
                type.isVariadic,
                type.recv?.let(::invoke),
            )
            is GoIRTupleType -> GoIRTupleType(type.elements.map(::invoke))
            else -> type
        }
        return result
    }
}

package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.GoIRApproximatedFunction
import org.opentaint.ir.go.api.GoIRBody
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRModelFunction
import org.opentaint.ir.go.api.GoIRNamedType
import org.opentaint.ir.go.api.GoIRPackage
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.api.GoIRTransformer
import org.opentaint.ir.go.impl.GoIRNamedTypeImpl
import org.opentaint.ir.go.impl.GoIRPackageImpl
import org.opentaint.ir.go.impl.functionEquals
import org.opentaint.ir.go.impl.functionHashCode
import org.opentaint.ir.go.type.GoIRAnonymousInterfaceType
import org.opentaint.ir.go.type.GoIRAnonymousInterfaceTypeRef
import org.opentaint.ir.go.type.GoIRArrayType
import org.opentaint.ir.go.type.GoIRBasicType
import org.opentaint.ir.go.type.GoIRChanType
import org.opentaint.ir.go.type.GoIRFuncType
import org.opentaint.ir.go.type.GoIRMapType
import org.opentaint.ir.go.type.GoIRNamedInterfaceType
import org.opentaint.ir.go.type.GoIRNamedTypeRef
import org.opentaint.ir.go.type.GoIRPointerType
import org.opentaint.ir.go.type.GoIRSliceType
import org.opentaint.ir.go.type.GoIRStructField
import org.opentaint.ir.go.type.GoIRStructType
import org.opentaint.ir.go.type.GoIRTupleType
import org.opentaint.ir.go.type.GoIRType
import org.opentaint.ir.go.type.GoIRTypeParamRef
import org.opentaint.ir.go.type.GoIRTypeParamType

internal data class GoIRModelDefinition(
    val source: String,
    val program: GoIRProgram,
    val targetPaths: Set<String>,
)

/** Applies partial Go models by intercepting the lookup of every modeled package. */
internal class GoIRModelTransformer(
    private val originalProgram: GoIRProgram,
    definitions: List<GoIRModelDefinition>,
) : GoIRTransformer {
    private val definitionsByTarget = linkedMapOf<String, GoIRModelDefinition>()
    private val modelDependencies = linkedMapOf<String, GoIRPackage>()

    init {
        definitions.forEach { definition ->
            definition.targetPaths.forEach { target ->
                val previous = definitionsByTarget.putIfAbsent(target, definition)
                require(previous == null) {
                    "Go package \"$target\" is modeled more than once " +
                        "(${previous?.source} and ${definition.source})"
                }
            }
        }
        // Bundled modules can describe dependencies that this project does not use.
        definitionsByTarget.entries.removeIf { (target, _) -> originalProgram.findPackage(target) == null }
        definitionsByTarget.forEach { (target, definition) ->
            validatePackage(target, definition)
        }
        definitions.forEach { definition ->
            if (definition.targetPaths.none { it in definitionsByTarget }) return@forEach
            definition.program.packages.forEach { (path, pkg) ->
                if (path !in definition.targetPaths && originalProgram.findPackage(path) == null) {
                    modelDependencies.putIfAbsent(path, pkg)
                }
            }
        }
    }

    override val additionalPackages: List<GoIRPackage> get() = modelDependencies.values.toList()

    override fun resolvePackage(importPath: String, next: () -> GoIRPackage?): GoIRPackage? {
        val definition = definitionsByTarget[importPath] ?: return next()
        val original = next() ?: return null
        return createPackage(original, definition.program.findPackage(importPath)!!)
    }

    private fun validatePackage(target: String, definition: GoIRModelDefinition) {
        val original = originalProgram.findPackage(target)
            ?: throw IllegalArgumentException(
                "invalid Go model ${definition.source}: target package \"$target\" was not found",
            )
        val model = definition.program.findPackage(target)
            ?: throw IllegalArgumentException(
                "invalid Go model ${definition.source}: model package \"$target\" was not found",
            )
        require(model.name == original.name) {
            "Go model package \"opentaint/$target\" has package name " +
                "\"${model.name}\", want \"${original.name}\" (the modeled package name)"
        }

        val originalFunctions = original.functions.associateBy { it.fullName }
        val initializers = initializerFunctions(model)
        model.functions.forEach { function ->
            if (function in initializers || function.parent != null) return@forEach
            val targetFunction = originalFunctions[function.fullName]
            if (targetFunction != null) {
                require(sameSignature(function, targetFunction)) {
                    "Go model function ${function.fullName} has a different signature from its target"
                }
            }
        }
        validateFields(original, model, definition.source)
    }

    private fun createPackage(original: GoIRPackage, model: GoIRPackage): GoIRPackage {
        val initializers = initializerFunctions(model)
        val modelFunctions = model.functions.filterNot { it in initializers }
        val modelByName = modelFunctions
            .filter { it.parent == null }
            .associateBy { it.fullName }
        val used = mutableSetOf<GoIRFunction>()
        val specializedAnonymousFunctions = mutableListOf<GoIRFunction>()
        val specializer = GoIRModelSpecializer(originalProgram)
        val result = GoIRPackageImpl(original.importPath, original.name, original.isStdlib, original.isDependency)
        original.functions.forEach { target ->
            val replacement = modelByName[target.fullName]
            val genericModel = target.originFullName?.let(modelByName::get)
            result.addFunction(
                if (replacement != null && replacement.bodyAvailable && sameSignature(replacement, target)) {
                    used += replacement
                    ApproximatedFunction(replacement, target)
                } else if (genericModel != null && genericModel.bodyAvailable) {
                    val specialized = specializer.specialize(genericModel, target)
                    specializedAnonymousFunctions += specialized.drop(1)
                    ApproximatedFunction(specialized.first(), target)
                } else {
                    target
                },
            )
        }
        specializedAnonymousFunctions.forEach { result.addFunction(ModelFunction(it)) }
        modelFunctions.filter { it !in used }.forEach { result.addFunction(ModelFunction(it)) }

        val functionsByName = buildMap { result.functions.forEach { putIfAbsent(it.fullName, it) } }
        val modelTypes = model.namedTypes.associateBy { it.name }
        original.namedTypes.forEach { target ->
            val modelType = modelTypes[target.name]
            result.addNamedType(modelType?.let { mergeNamedType(target, it, result, functionsByName) } ?: target)
        }
        model.namedTypes.filter { original.findNamedType(it.name) == null }.forEach(result::addNamedType)
        (original.globals + model.globals).forEach { if (result.findGlobal(it.name) == null) result.addGlobal(it) }
        (original.constants + model.constants).forEach { if (result.findConstant(it.name) == null) result.addConst(it) }
        (original.imports + model.imports).distinctBy { it.importPath }.forEach { result._imports += it }
        result.initFunction = original.initFunction
        return result
    }

    private fun mergeNamedType(
        original: GoIRNamedType,
        model: GoIRNamedType,
        pkg: GoIRPackage,
        functionsByName: Map<String, GoIRFunction>,
    ): GoIRNamedType {
        val originalNames = original.fields.mapTo(mutableSetOf()) { it.name }
        val fields = original.fields + model.fields.filter { it.name !in originalNames }
            .mapIndexed { index, field -> field.copy(index = original.fields.size + index) }
        val originalStruct = original.underlying as? GoIRStructType
        val underlying = originalStruct?.let { struct ->
            GoIRStructType(
                fields.map { GoIRStructField(it.name, it.type, it.isEmbedded, it.tag) },
                struct.structTypeRef,
            )
        } ?: original.underlying
        val result = GoIRNamedTypeImpl(
            original.name, original.fullName, pkg, underlying, original.kind, original.position, original.typeParams,
        )
        fields.mapTo(result._fields) { it.copy(enclosingType = result) }
        effectiveMethods(original.methods, model.methods, functionsByName).let(result._methods::addAll)
        effectiveMethods(original.pointerMethods, model.pointerMethods, functionsByName)
            .let(result._pointerMethods::addAll)
        result._interfaceMethods += original.interfaceMethods
        result._embeddedInterfaces += original.embeddedInterfaces
        return result
    }

    private fun effectiveMethods(
        targetMethods: List<GoIRFunction>,
        modelMethods: List<GoIRFunction>,
        functionsByName: Map<String, GoIRFunction>,
    ): List<GoIRFunction> {
        val targetNames = targetMethods.mapTo(mutableSetOf()) { it.fullName }
        return (targetMethods + modelMethods.filter { it.fullName !in targetNames })
            .map { functionsByName[it.fullName] ?: it }
    }

    private fun validateFields(original: GoIRPackage, model: GoIRPackage, source: String) {
        model.namedTypes.forEach { modelType ->
            val targetType = original.findNamedType(modelType.name) ?: return@forEach
            val targetFields = targetType.fields.associateBy { it.name }
            modelType.fields.forEach { modelField ->
                val targetField = targetFields[modelField.name] ?: return@forEach
                require(sameType(modelField.type, targetField.type)) {
                    "invalid Go model $source: field ${targetType.fullName}.${modelField.name} " +
                        "has a different type from its target"
                }
            }
        }
    }

    private fun sameSignature(model: GoIRFunction, target: GoIRFunction): Boolean =
        sameType(model.signature, target.signature) &&
            model.isMethod == target.isMethod &&
            model.isPointerReceiver == target.isPointerReceiver

    private fun sameType(first: GoIRType, second: GoIRType): Boolean =
        sameType(first, second, mutableListOf())

    private fun sameType(
        first: GoIRType,
        second: GoIRType,
        active: MutableList<Pair<GoIRType, GoIRType>>,
    ): Boolean {
        if (first === second) return true
        if (active.any { (left, right) -> left === first && right === second }) return true
        active += first to second
        return when {
            first is GoIRBasicType && second is GoIRBasicType -> first.kind == second.kind
            first is GoIRPointerType && second is GoIRPointerType ->
                sameType(first.elem, second.elem, active)
            first is GoIRArrayType && second is GoIRArrayType ->
                first.length == second.length && sameType(first.elem, second.elem, active)
            first is GoIRSliceType && second is GoIRSliceType ->
                sameType(first.elem, second.elem, active)
            first is GoIRMapType && second is GoIRMapType ->
                sameType(first.key, second.key, active) && sameType(first.value, second.value, active)
            first is GoIRChanType && second is GoIRChanType ->
                first.direction == second.direction && sameType(first.elem, second.elem, active)
            first is GoIRStructType && second is GoIRStructType ->
                first.structTypeRef?.fullRefName == second.structTypeRef?.fullRefName &&
                    first.fields.size == second.fields.size &&
                    first.fields.zip(second.fields).all { (left, right) ->
                        left.name == right.name && left.isEmbedded == right.isEmbedded &&
                            left.tag == right.tag && sameType(left.type, right.type, active)
                    }
            first is GoIRNamedTypeRef && second is GoIRNamedTypeRef ->
                first.typeRef.fullRefName == second.typeRef.fullRefName &&
                    sameTypes(first.typeArgs, second.typeArgs, active)
            first is GoIRFuncType && second is GoIRFuncType ->
                first.isVariadic == second.isVariadic &&
                    nullableTypeEqual(first.recv, second.recv, active) &&
                    sameTypes(first.params, second.params, active) &&
                    sameTypes(first.results, second.results, active)
            first is GoIRTupleType && second is GoIRTupleType ->
                sameTypes(first.elements, second.elements, active)
            first is GoIRTypeParamType && second is GoIRTypeParamType ->
                first.paramIndex == second.paramIndex && first.name == second.name &&
                    sameType(first.constraint, second.constraint, active)
            first is GoIRTypeParamRef && second is GoIRTypeParamRef ->
                first.paramIndex == second.paramIndex && first.name == second.name
            first is GoIRAnonymousInterfaceTypeRef && second is GoIRAnonymousInterfaceTypeRef ->
                sameAnonymousInterface(first.interfaceType, second.interfaceType, active)
            first is GoIRAnonymousInterfaceType && second is GoIRAnonymousInterfaceType ->
                sameAnonymousInterface(first, second, active)
            first is GoIRNamedInterfaceType && second is GoIRNamedInterfaceType ->
                first.interfaceTypeRef.fullRefName == second.interfaceTypeRef.fullRefName
            else -> false
        }
    }

    private fun sameAnonymousInterface(
        first: GoIRAnonymousInterfaceType,
        second: GoIRAnonymousInterfaceType,
        active: MutableList<Pair<GoIRType, GoIRType>>,
    ): Boolean = first.methods.size == second.methods.size &&
        first.methods.zip(second.methods).all { (left, right) ->
            left.name == right.name && sameType(left.signature, right.signature, active)
        } && sameTypes(first.embeds, second.embeds, active)

    private fun sameTypes(
        first: List<GoIRType>,
        second: List<GoIRType>,
        active: MutableList<Pair<GoIRType, GoIRType>>,
    ): Boolean = first.size == second.size &&
        first.zip(second).all { (left, right) -> sameType(left, right, active) }

    private fun nullableTypeEqual(
        first: GoIRType?,
        second: GoIRType?,
        active: MutableList<Pair<GoIRType, GoIRType>>,
    ): Boolean = when {
        first == null -> second == null
        second == null -> false
        else -> sameType(first, second, active)
    }

    private fun initializerFunctions(pkg: GoIRPackage): Set<GoIRFunction> {
        val result = pkg.functions
            .filterTo(mutableSetOf()) { it.name == "init" || it.name.startsWith("init#") }
        do {
            val oldSize = result.size
            pkg.functions.forEach { function ->
                val parentName = function.parent?.fullName
                if (parentName != null && result.any { it.fullName == parentName }) {
                    result += function
                }
            }
        } while (result.size != oldSize)
        return result
    }
}


private open class ModelFunction(protected val implementation: GoIRFunction) : GoIRModelFunction,
    GoIRFunction by implementation, GoIRBodyReader {
    override fun readBody(owner: GoIRFunction, context: GoIRBodyContext): GoIRBody? =
        (implementation as GoIRBodyReader).readBody(owner, context)
    override val isSynthetic: Boolean get() = true
    override fun equals(other: Any?): Boolean = functionEquals(other)
    override fun hashCode(): Int = functionHashCode()
    override fun toString(): String = "GoIRModelFunction($fullName)"
}

private class ApproximatedFunction(
    implementation: GoIRFunction,
    override val original: GoIRFunction,
) : ModelFunction(implementation), GoIRApproximatedFunction

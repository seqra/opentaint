package org.opentaint.ir.go.client

import org.opentaint.ir.go.api.GoIRConst
import org.opentaint.ir.go.api.GoIRFunction
import org.opentaint.ir.go.api.GoIRGlobal
import org.opentaint.ir.go.api.GoIRGlobalReference
import org.opentaint.ir.go.api.GoIRNamedType
import org.opentaint.ir.go.api.GoIRPackage
import org.opentaint.ir.go.api.GoIRProgram
import org.opentaint.ir.go.api.GoIRTransformer
import org.opentaint.ir.go.api.GoIrFunctionReference
import org.opentaint.ir.go.impl.GoIRApproximatedFunctionImpl
import org.opentaint.ir.go.impl.GoIRConstImpl
import org.opentaint.ir.go.impl.GoIRFunctionImpl
import org.opentaint.ir.go.impl.GoIRGlobalImpl
import org.opentaint.ir.go.impl.GoIRModelFunctionImpl
import org.opentaint.ir.go.impl.GoIRNamedTypeImpl
import org.opentaint.ir.go.impl.GoIRPackageImpl
import org.opentaint.ir.go.impl.GoIRProgramImpl
import org.opentaint.ir.go.type.*

/** A deserialized model module and the target path of each of its model-addressed (`opentaint/<target>`) packages. */
internal class GoIRModelDefinition private constructor(
    val source: String,
    val program: GoIRProgram,
    val targets: Map<String, String>,
) {
    companion object {
        fun create(source: String, program: GoIRProgram): GoIRModelDefinition {
            val targets = program.packages.values
                .filterNot { it.isDependency || it.isStdlib || it.importPath == UNIVERSE_PACKAGE_PATH }
                .associate { pkg ->
                    require(pkg.importPath.startsWith(GO_MODEL_PREFIX)) {
                        "Go model package \"${pkg.importPath}\" is not model-addressed, " +
                            "its import path must be ${GO_MODEL_PREFIX}<target-import-path>"
                    }
                    val target = pkg.importPath.removePrefix(GO_MODEL_PREFIX)
                    require(target.isNotEmpty()) {
                        "Go model package \"${pkg.importPath}\" has an empty target package"
                    }
                    pkg.importPath to target
                }
            require(targets.isNotEmpty()) {
                "Go model contains no model-addressed packages, expected at least one package " +
                    "under $GO_MODEL_PREFIX"
            }
            return GoIRModelDefinition(source, program, targets)
        }
    }
}

/** Applies partial Go models by intercepting the lookup of every modeled package. */
internal class GoIRModelTransformer(
    private val program: GoIRProgramImpl,
    definitions: List<GoIRModelDefinition>,
) : GoIRTransformer {
    private val scopesByTarget = linkedMapOf<String, ModelScope>()
    private val modelDependencies = linkedMapOf<String, GoIRPackage>()

    init {
        val definitionsByTarget = linkedMapOf<String, GoIRModelDefinition>()
        definitions.forEach { definition ->
            definition.targets.values.forEach { target ->
                val previous = definitionsByTarget.putIfAbsent(target, definition)
                require(previous == null) {
                    "Go package \"$target\" is modeled more than once " +
                        "(${previous?.source} and ${definition.source})"
                }
            }
        }
        // Bundled modules can describe dependencies that this project does not use.
        definitionsByTarget.entries.removeIf { (target, _) -> program.declaredPackage(target) == null }
        val scopes = definitionsByTarget.values.distinct().associateWith { ModelScope(it) }
        definitionsByTarget.forEach { (target, definition) -> scopesByTarget[target] = scopes.getValue(definition) }
        scopesByTarget.forEach { (target, scope) -> scope.validatePackage(target) }
        scopes.keys.forEach { definition ->
            definition.program.packages.forEach { (path, pkg) ->
                if (path !in definition.targets && program.declaredPackage(path) == null) {
                    modelDependencies.putIfAbsent(path, pkg)
                }
            }
        }
    }

    override val additionalPackages: List<GoIRPackage> get() = modelDependencies.values.toList()

    override fun resolvePackage(importPath: String, next: () -> GoIRPackage?): GoIRPackage? {
        val scope = scopesByTarget[importPath] ?: return next()
        val original = next() ?: return null
        return scope.createPackage(original)
    }

    /** Resolves the symbols of one model module into the program it models. */
    private inner class ModelScope(val definition: GoIRModelDefinition) {
        private val modelPaths = definition.targets.keys.sortedByDescending(String::length)
        private val modelPackages = definition.targets.entries.associate { (model, target) ->
            target to definition.program.findPackage(model)!!
        }

        // Anonymous interface IDs are local to each wire program, so model definitions get fresh program IDs.
        private val interfaceIds: Map<Int, Int> = run {
            var nextId = (program.anonymousInterfaces.keys.maxOrNull() ?: -1) + 1
            definition.program.anonymousInterfaces.keys.associateWith { nextId++ }
        }

        init {
            definition.program.anonymousInterfaces.values.forEach {
                program.addAnonymousInterface(type(it) as GoIRAnonymousInterfaceType)
            }
        }

        private fun path(importPath: String) = definition.targets[importPath] ?: importPath

        private fun symbol(fullName: String) = modelPaths.fold(fullName) { result, modelPath ->
            result.replace(modelPath, definition.targets.getValue(modelPath))
        }

        private fun reference(ref: NamedTypeRef) =
            ref.copy(refTypePkg = path(ref.refTypePkg)).also { it.program = program }

        fun type(value: GoIRType): GoIRType = when (value) {
            is GoIRTypeParamType -> value.copy(constraint = type(value.constraint))
            is GoIRTypeParamRef -> value
            is GoIRPointerType -> GoIRPointerType(type(value.elem))
            is GoIRArrayType -> GoIRArrayType(type(value.elem), value.length)
            is GoIRSliceType -> GoIRSliceType(type(value.elem))
            is GoIRMapType -> GoIRMapType(type(value.key), type(value.value))
            is GoIRChanType -> GoIRChanType(type(value.elem), value.direction)
            is GoIRStructType -> GoIRStructType(
                value.fields.map { GoIRStructField(it.name, type(it.type), it.isEmbedded, it.tag) },
                value.structTypeRef?.let(::reference),
            )
            is GoIRNamedTypeRef -> GoIRNamedTypeRef(reference(value.typeRef), value.typeArgs.map(::type))
            is GoIRNamedInterfaceType -> GoIRNamedInterfaceType(
                value.methods.map { GoIRInterfaceMethodSig(it.name, type(it.signature) as GoIRFuncType) },
                value.embeds.map(::type),
                reference(value.interfaceTypeRef),
            )
            is GoIRAnonymousInterfaceTypeRef -> GoIRAnonymousInterfaceTypeRef(interfaceIds.getValue(value.id))
                .also { it.program = program }
            is GoIRAnonymousInterfaceType -> GoIRAnonymousInterfaceType(
                interfaceIds.getValue(value.id),
                value.methods.map { GoIRInterfaceMethodSig(it.name, type(it.signature) as GoIRFuncType) },
                value.embeds.map(::type),
            )
            is GoIRFuncType -> GoIRFuncType(
                value.params.map(::type),
                value.results.map(::type),
                value.isVariadic,
                value.recv?.let(::type),
            )
            is GoIRTupleType -> GoIRTupleType(value.elements.map(::type))
            else -> value
        }

        /** Decodes model bodies against the modeled program: target paths, program IDs and merged field layouts. */
        val context = object : GoIRBodyContext() {
            override fun type(type: GoIRType) = this@ModelScope.type(type)
            override fun function(reference: GoIrFunctionReference) = reference
                .copy(pkg = path(reference.pkg), signature = type(reference.signature) as GoIRFuncType)
                .also { it.program = program }
            override fun global(reference: GoIRGlobalReference) =
                reference.copy(pkg = path(reference.pkg)).also { it.program = program }
            override fun fieldIndex(type: GoIRType, index: Int, name: String): Int {
                fun named(type: GoIRType): GoIRNamedType? = when (type) {
                    is GoIRPointerType -> named(type.elem)
                    is GoIRNamedTypeRef -> type.namedType
                    is GoIRStructType -> type.namedType
                    else -> null
                }
                return named(type)?.fields?.firstOrNull { it.name == name }?.index ?: index
            }
        }

        private fun function(model: GoIRFunction, pkg: GoIRPackage, original: GoIRFunction?): GoIRFunction =
            modelFunction(
                original, model.name, symbol(model.fullName), pkg, type(model.signature) as GoIRFuncType,
                model.params.map { it.copy(type = type(it.type)) },
                model.freeVars.map { it.copy(type = type(it.type)) },
                model.position, model.isMethod, model.isPointerReceiver, model.isExported, model.syntheticKind,
                model.hasBody, model.parent?.let(context::function), model.anonymousFunctions.map(context::function),
                model.typeParams.map { it.copy(constraint = type(it.constraint)) },
                model.originFullName?.let(::symbol), model.typeArgs.map(::type),
            ).also { function ->
                if (!model.bodyAvailable) return@also
                function.setBodyReader { owner, _ ->
                    (model as GoIRFunctionImpl).readBody(owner, context)
                        ?: error("Go model ${model.fullName} has no body")
                }
            }

        fun validatePackage(target: String) {
            val original = program.declaredPackage(target)!!
            val model = modelPackages[target]
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
                val targetFunction = originalFunctions[symbol(function.fullName)]
                if (targetFunction != null) {
                    require(sameSignature(function, targetFunction)) {
                        "Go model function ${symbol(function.fullName)} has a different signature from its target"
                    }
                }
            }
            model.namedTypes.forEach { modelType ->
                val targetType = original.findNamedType(modelType.name) ?: return@forEach
                val targetFields = targetType.fields.associateBy { it.name }
                modelType.fields.forEach { modelField ->
                    val targetField = targetFields[modelField.name] ?: return@forEach
                    require(sameType(type(modelField.type), targetField.type)) {
                        "invalid Go model ${definition.source}: field ${targetType.fullName}.${modelField.name} " +
                            "has a different type from its target"
                    }
                }
            }
        }

        fun createPackage(original: GoIRPackage): GoIRPackage {
            val model = modelPackages.getValue(original.importPath)
            val initializers = initializerFunctions(model)
            val modelFunctions = model.functions.filterNot { it in initializers }
            val modelByName = modelFunctions
                .filter { it.parent == null }
                .associateBy { symbol(it.fullName) }
            val used = mutableSetOf<GoIRFunction>()
            val specializedAnonymousFunctions = mutableListOf<GoIRFunction>()
            val result = GoIRPackageImpl(original.importPath, original.name, original.isStdlib, original.isDependency)
            val specializer = GoIRModelSpecializer(program, result, context, ::symbol)
            original.functions.forEach { target ->
                val replacement = modelByName[target.fullName]
                val genericModel = target.originFullName?.let(modelByName::get)
                result.addFunction(
                    if (replacement != null && replacement.bodyAvailable && sameSignature(replacement, target)) {
                        used += replacement
                        function(replacement, result, target)
                    } else if (genericModel != null && genericModel.bodyAvailable) {
                        val specialized = specializer.specialize(genericModel, target)
                        specializedAnonymousFunctions += specialized.drop(1)
                        specialized.first()
                    } else {
                        target
                    },
                )
            }
            specializedAnonymousFunctions.forEach(result::addFunction)
            modelFunctions.filter { it !in used }.forEach { result.addFunction(function(it, result, null)) }

            val functionsByName = buildMap { result.functions.forEach { putIfAbsent(it.fullName, it) } }
            val modelTypes = model.namedTypes.associateBy { it.name }
            original.namedTypes.forEach { target ->
                result.addNamedType(modelTypes[target.name]?.let { namedType(target, it, result, functionsByName) } ?: target)
            }
            model.namedTypes.filter { original.findNamedType(it.name) == null }.forEach {
                result.addNamedType(namedType(null, it, result, functionsByName))
            }
            original.globals.forEach(result::addGlobal)
            model.globals.filter { result.findGlobal(it.name) == null }.forEach { result.addGlobal(global(it, result)) }
            original.constants.forEach(result::addConst)
            model.constants.filter { result.findConstant(it.name) == null }.forEach { result.addConst(constant(it, result)) }
            result._imports += original.imports
            result._imports += model.imports.mapNotNull { modelDependencies[it.importPath] }
                .filter { dependency -> result._imports.none { it.importPath == dependency.importPath } }
            result.initFunction = original.initFunction
            return result
        }

        private fun global(model: GoIRGlobal, pkg: GoIRPackage) =
            GoIRGlobalImpl(model.name, symbol(model.fullName), type(model.type), pkg, model.isExported, model.position)

        private fun constant(model: GoIRConst, pkg: GoIRPackage) = GoIRConstImpl(
            model.name, symbol(model.fullName), type(model.type), model.value, pkg, model.isExported, model.position,
        )

        private fun namedType(
            original: GoIRNamedType?,
            model: GoIRNamedType,
            pkg: GoIRPackage,
            functionsByName: Map<String, GoIRFunction>,
        ): GoIRNamedType {
            val originalFields = original?.fields.orEmpty()
            val originalNames = originalFields.mapTo(mutableSetOf()) { it.name }
            val fields = originalFields + model.fields.filter { it.name !in originalNames }
                .mapIndexed { index, field -> field.copy(type = type(field.type), index = originalFields.size + index) }
            val underlying = when (val declared = original?.underlying ?: type(model.underlying)) {
                is GoIRStructType -> GoIRStructType(
                    fields.map { GoIRStructField(it.name, it.type, it.isEmbedded, it.tag) },
                    declared.structTypeRef,
                )
                else -> declared
            }
            val result = GoIRNamedTypeImpl(
                model.name, symbol(model.fullName), pkg, underlying,
                original?.kind ?: model.kind,
                original?.position ?: model.position,
                original?.typeParams ?: model.typeParams.map { it.copy(constraint = type(it.constraint)) },
            )
            fields.mapTo(result._fields) { it.copy(enclosingType = result) }
            result._methods += methods(original?.methods.orEmpty(), model.methods, functionsByName)
            result._pointerMethods += methods(original?.pointerMethods.orEmpty(), model.pointerMethods, functionsByName)
            result._interfaceMethods += original?.interfaceMethods ?: model.interfaceMethods.map {
                it.copy(signature = type(it.signature) as GoIRFuncType, enclosingInterface = result)
            }
            result._embeddedInterfaces += original?.embeddedInterfaces ?: model.embeddedInterfaces.map { embedded ->
                pkg.findNamedType(embedded.name)?.takeIf { path(embedded.pkg.importPath) == pkg.importPath } ?: embedded
            }
            return result
        }

        private fun methods(
            targetMethods: List<GoIRFunction>,
            modelMethods: List<GoIRFunction>,
            functionsByName: Map<String, GoIRFunction>,
        ): List<GoIRFunction> {
            val targetNames = targetMethods.mapTo(mutableSetOf()) { it.fullName }
            return targetMethods.map { functionsByName[it.fullName] ?: it } +
                modelMethods.map { symbol(it.fullName) }.filter { it !in targetNames }.mapNotNull(functionsByName::get)
        }

        private fun sameSignature(model: GoIRFunction, target: GoIRFunction): Boolean =
            sameType(type(model.signature), target.signature) &&
                model.isMethod == target.isMethod &&
                model.isPointerReceiver == target.isPointerReceiver
    }

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


internal fun modelFunction(
    original: GoIRFunction?,
    name: String,
    fullName: String,
    pkg: GoIRPackage?,
    signature: GoIRFuncType,
    params: List<org.opentaint.ir.go.api.GoIRParameter>,
    freeVars: List<org.opentaint.ir.go.api.GoIRFreeVar>,
    position: org.opentaint.ir.go.api.GoIRPosition?,
    isMethod: Boolean,
    isPointerReceiver: Boolean,
    isExported: Boolean,
    syntheticKind: String?,
    hasBody: Boolean,
    parent: GoIrFunctionReference?,
    anonymousFunctions: List<GoIrFunctionReference>,
    typeParams: List<org.opentaint.ir.go.api.GoIRTypeParamDecl>,
    originFullName: String?,
    typeArgs: List<GoIRType>,
): GoIRFunctionImpl = if (original == null) {
    GoIRModelFunctionImpl(
        name, fullName, pkg, signature, params, freeVars, position, isMethod, isPointerReceiver, isExported,
        syntheticKind, hasBody, parent, anonymousFunctions, typeParams, originFullName, typeArgs,
    )
} else {
    GoIRApproximatedFunctionImpl(
        original, name, fullName, pkg, signature, params, freeVars, position, isMethod, isPointerReceiver,
        isExported, syntheticKind, hasBody, parent, anonymousFunctions, typeParams, originFullName, typeArgs,
    )
}

private const val GO_MODEL_PREFIX = "opentaint/"
private const val UNIVERSE_PACKAGE_PATH = "<universe>"

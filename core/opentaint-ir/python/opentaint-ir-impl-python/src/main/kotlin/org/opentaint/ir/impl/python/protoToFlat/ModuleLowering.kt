package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.impl.python.flat.*
import org.opentaint.ir.impl.python.protoToFlat.cfg.CfgBuild
import org.opentaint.ir.impl.python.proto.MypyAssignmentStmtProto
import org.opentaint.ir.impl.python.proto.MypyClassDefProto
import org.opentaint.ir.impl.python.proto.MypyDefinitionProto
import org.opentaint.ir.impl.python.proto.MypyModuleProto
import org.opentaint.ir.impl.python.proto.MypyStmtProto

internal object ModuleLowering {

    private val ENUM_BASE_CLASSES = setOf(
        "enum.Enum", "enum.IntEnum", "enum.Flag", "enum.IntFlag",
    )

    fun lower(astModule: MypyModuleProto): FlatModuleIR {
        val context = ModuleContext(moduleName = astModule.name)

        for (error in astModule.errorsList) {
            context.reportError(error, astModule.name, "MypyBuildError")
        }

        // todo: imports nested in module-level control flow (`try: import …`,
        //  `if cond: import …`) never reach here — `_serialize_definitions` in
        //  ast_serializer.py drops module-level `If` / `Try` / `With` entirely. Such imports
        //  mis-classify as `FlatGlobalRef("scope.x")` when mypy can't resolve them.
        val moduleFields = mutableListOf<FlatModuleField>()
        val moduleInitStmts = mutableListOf<MypyStmtProto>()
        val defQueue = mutableListOf<MypyDefinitionProto>()

        for (def in astModule.defsList) {
            when (def.kindCase) {
                MypyDefinitionProto.KindCase.CLASS_DEF,
                MypyDefinitionProto.KindCase.FUNC_DEF,
                MypyDefinitionProto.KindCase.DECORATOR -> defQueue.add(def)
                MypyDefinitionProto.KindCase.ASSIGNMENT -> {
                    val stmt = def.assignment
                    if (stmt.hasAssignment()) {
                        moduleFields.addAll(extractFields(stmt.assignment) { name, type ->
                            FlatModuleField(name = name, type = type, hasInitializer = true)
                        })
                    }
                    moduleInitStmts.add(stmt)
                }
                else -> {}
            }
        }

        val moduleInit = lowerModuleInit(context, moduleInitStmts)

        val classes = mutableListOf<FlatClass>()
        val topLevelFunctions = mutableListOf<FlatFunctionIR>()
        for (def in defQueue) {
            when (def.kindCase) {
                MypyDefinitionProto.KindCase.CLASS_DEF ->
                    classes.add(lowerClass(context, def.classDef, enclosingQualifier = null))
                MypyDefinitionProto.KindCase.FUNC_DEF,
                MypyDefinitionProto.KindCase.DECORATOR ->
                    topLevelFunctions.add(lowerFuncOrDecorator(context, def, enclosingClassQualifiedName = null))
                else -> error("defQueue must contain only class/func/decorator defs; got ${def.kindCase}")
            }
        }

        val syntheticFunctions = context.registeredFunctions

        val rawModule = FlatModuleIR(
            moduleName = astModule.name,
            path = astModule.path,
            functions = topLevelFunctions + syntheticFunctions,
            moduleInit = moduleInit,
            classes = classes,
            fields = moduleFields,
            imports = astModule.importsList,
            diagnostics = context.diagnostics,
        )

        // TODO use it as a transform?
        return ResolvedCalleeNormalizer.normalize(rawModule)
    }

    private fun lowerClass(
        context: ModuleContext,
        classDef: MypyClassDefProto,
        enclosingQualifier: String?,
    ): FlatClass {
        val qualifiedName = classDef.fullname.ifEmpty {
            "${enclosingQualifier ?: context.moduleName}.${classDef.name}"
        }

        val methods = mutableListOf<FlatFunctionIR>()
        val classFields = mutableListOf<FlatClassField>()
        val nestedClasses = mutableListOf<FlatClass>()

        for (def in classDef.bodyList) {
            when (def.kindCase) {
                MypyDefinitionProto.KindCase.FUNC_DEF,
                MypyDefinitionProto.KindCase.DECORATOR ->
                    methods.add(lowerFuncOrDecorator(context, def, enclosingClassQualifiedName = qualifiedName))
                MypyDefinitionProto.KindCase.ASSIGNMENT -> {
                    // todo: `assignment` slot also carries module-level `Import` / `ImportFrom`, drop them
                    if (def.assignment.hasAssignment()) {
                        // todo: `is_class_var` flag is not threaded
                        classFields.addAll(extractFields(def.assignment.assignment) { name, type ->
                            FlatClassField(name = name, type = type, isClassVar = false)
                        })
                    }
                }
                MypyDefinitionProto.KindCase.CLASS_DEF ->
                    nestedClasses.add(lowerClass(context, def.classDef, enclosingQualifier = qualifiedName))
                else -> {}
            }
        }

        val decorators = DecoratorLowering.fromClassDef(classDef)
        val isEnum = classDef.baseClassesList.any { it in ENUM_BASE_CLASSES }
        val isDataclass = classDef.isDataclass || decorators.any { it.name == "dataclass" }

        return FlatClass(
            name = classDef.name,
            qualifiedName = qualifiedName,
            baseClasses = classDef.baseClassesList,
            mro = classDef.mroList,
            methods = methods,
            fields = classFields,
            nestedClasses = nestedClasses,
            decorators = decorators,
            isAbstract = classDef.isAbstract,
            isDataclass = isDataclass,
            isEnum = isEnum,
        )
    }

    private fun lowerFuncOrDecorator(
        context: ModuleContext,
        def: MypyDefinitionProto,
        enclosingClassQualifiedName: String?,
    ): FlatFunctionIR = when (def.kindCase) {
        MypyDefinitionProto.KindCase.FUNC_DEF -> FunctionLowering.lowerTopLevel(
            module = context,
            funcDef = def.funcDef,
            decorators = DecoratorLowering.fromFuncDef(def.funcDef),
            enclosingClassQualifiedName = enclosingClassQualifiedName,
        )
        MypyDefinitionProto.KindCase.DECORATOR -> FunctionLowering.lowerTopLevel(
            module = context,
            funcDef = def.decorator.func,
            decorators = DecoratorLowering.fromDecoratorDef(def.decorator, context.imports),
            enclosingClassQualifiedName = enclosingClassQualifiedName,
        )
        else -> error("lowerFuncOrDecorator: unexpected kind ${def.kindCase}")
    }

    private inline fun <T> extractFields(
        assignment: MypyAssignmentStmtProto,
        factory: (name: String, type: FlatType) -> T,
    ): List<T> = assignment.lvaluesList.mapNotNull { lvalue ->
        if (!lvalue.hasNameExpr()) return@mapNotNull null
        factory(
            lvalue.nameExpr.name,
            if (lvalue.hasExprType()) TypeLowering.convertType(lvalue.exprType) else FlatAnyType,
        )
    }

    private fun lowerModuleInit(
        context: ModuleContext,
        assignments: List<MypyStmtProto>,
    ): FlatFunctionIR {
        val cfg = CfgBuild.buildModuleInitCfg(context, assignments)
        return FlatFunctionIR(
            name = "__module_init__",
            qualifiedName = "${context.moduleName}.__module_init__",
            parentQualifiedName = null,
            kind = FlatFunctionKind.MODULE_INIT,
            cfg = cfg,
            parameters = emptyList(),
            returnType = FlatAnyType,
            isAsync = false,
            isGenerator = false,
            decorators = emptyList(),
        )
    }
}

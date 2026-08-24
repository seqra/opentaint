package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.api.python.PythonNames
import org.opentaint.ir.impl.python.flat.*
import org.opentaint.ir.impl.python.protoToFlat.cfg.CfgBuild
import org.opentaint.ir.impl.python.proto.MypyFuncDefProto
import org.opentaint.ir.impl.python.proto.MypyLambdaExprProto

internal object FunctionLowering {

    fun lowerTopLevel(
        module: ModuleContext,
        funcDef: MypyFuncDefProto,
        decorators: List<FlatDecorator>,
        enclosingClassQualifiedName: String?,
    ): FlatFunctionIR {
        val qualifiedName = qualifyTopLevel(module.moduleName, enclosingClassQualifiedName, funcDef)
        val parameters = TypeLowering.convertParameters(funcDef.argumentsList)
        val isConstructor = enclosingClassQualifiedName != null && funcDef.name == PythonNames.INIT_METHOD
        val cfgResult = if (funcDef.hasBody()) {
            CfgBuild.buildFunctionCfg(
                module = module,
                qualifiedName = qualifiedName,
                functionName = funcDef.name,
                body = funcDef.body,
                parameters = parameters,
                sourceLabel = funcDef.name,
                imports = module.imports.nestedChild(),
                isConstructor = isConstructor,
            )
        } else CfgBuild.CfgBuildResult.EMPTY

        return FlatFunctionIR(
            name = funcDef.name,
            qualifiedName = qualifiedName,
            parentQualifiedName = null,
            kind = if (enclosingClassQualifiedName != null) FlatFunctionKind.METHOD else FlatFunctionKind.TOP_LEVEL,
            cfg = cfgResult.cfg,
            parameters = parameters,
            returnType = if (funcDef.hasReturnType()) TypeLowering.convertType(funcDef.returnType) else FlatAnyType,
            isAsync = funcDef.isAsync,
            isGenerator = funcDef.isGenerator,
            decorators = decorators,
            nonlocalNames = cfgResult.nonlocalNames,
            globalNames = cfgResult.globalNames,
        )
    }

    fun lowerNestedFunction(
        module: ModuleContext,
        funcDef: MypyFuncDefProto,
        decorators: List<FlatDecorator>,
        enclosingQualifiedName: String,
        enclosingName: String,
        enclosingImports: ImportManager,
    ): FlatFunctionIR {
        val uniqueName = module.freshNestedName(enclosingName, funcDef.name)
        val qualifiedName = "${module.moduleName}.$uniqueName"
        val parameters = TypeLowering.convertParameters(funcDef.argumentsList)

        val cfgResult = if (funcDef.hasBody()) {
            CfgBuild.buildFunctionCfg(
                module = module,
                qualifiedName = qualifiedName,
                functionName = uniqueName,
                body = funcDef.body,
                parameters = parameters,
                sourceLabel = funcDef.name,
                errorPrefix = "Failed to build CFG for nested $qualifiedName",
                imports = enclosingImports.nestedChild(),
            )
        } else CfgBuild.CfgBuildResult.EMPTY

        return FlatFunctionIR(
            name = uniqueName,
            qualifiedName = qualifiedName,
            parentQualifiedName = enclosingQualifiedName,
            kind = FlatFunctionKind.NESTED_DEF,
            cfg = cfgResult.cfg,
            parameters = parameters,
            returnType = if (funcDef.hasReturnType()) TypeLowering.convertType(funcDef.returnType) else FlatAnyType,
            isAsync = funcDef.isAsync,
            isGenerator = funcDef.isGenerator,
            decorators = decorators,
            nonlocalNames = cfgResult.nonlocalNames,
            globalNames = cfgResult.globalNames,
        )
    }

    fun lowerLambda(
        module: ModuleContext,
        expr: MypyLambdaExprProto,
        parentQualifiedName: String?,
        enclosingImports: ImportManager,
    ): FlatFunctionIR {
        val name = module.freshLambdaName()
        val qualifiedName = "${module.moduleName}.$name"
        val parameters = TypeLowering.convertParameters(expr.argumentsList)

        val cfgResult = CfgBuild.buildFunctionCfg(
            module = module,
            qualifiedName = qualifiedName,
            functionName = name,
            body = expr.body,
            parameters = parameters,
            sourceLabel = name,
            errorPrefix = "Failed to build CFG for lambda $qualifiedName",
            imports = enclosingImports.nestedChild(),
        )

        return FlatFunctionIR(
            name = name,
            qualifiedName = qualifiedName,
            parentQualifiedName = parentQualifiedName,
            kind = FlatFunctionKind.LAMBDA,
            cfg = cfgResult.cfg,
            parameters = parameters,
            returnType = if (expr.hasReturnType()) TypeLowering.convertType(expr.returnType) else FlatAnyType,
            isAsync = false,
            isGenerator = false,
            decorators = emptyList(),
            nonlocalNames = cfgResult.nonlocalNames,
            globalNames = cfgResult.globalNames,
        )
    }

    private fun qualifyTopLevel(
        moduleName: String,
        enclosingClassQualifiedName: String?,
        funcDef: MypyFuncDefProto,
    ): String = when {
        enclosingClassQualifiedName != null -> "$enclosingClassQualifiedName.${funcDef.name}"
        funcDef.fullname.isNotEmpty() -> funcDef.fullname
        else -> "$moduleName.${funcDef.name}"
    }
}

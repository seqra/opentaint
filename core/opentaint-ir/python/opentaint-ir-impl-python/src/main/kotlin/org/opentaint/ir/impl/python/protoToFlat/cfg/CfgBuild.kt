package org.opentaint.ir.impl.python.protoToFlat.cfg

import org.opentaint.ir.impl.python.flat.FlatAssign
import org.opentaint.ir.impl.python.flat.FlatCFG
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatParameter
import org.opentaint.ir.impl.python.flat.FlatParameterRef
import org.opentaint.ir.impl.python.protoToFlat.ImportManager
import org.opentaint.ir.impl.python.protoToFlat.ModuleContext
import org.opentaint.ir.impl.python.protoToFlat.recordImports
import org.opentaint.ir.impl.python.protoToFlat.recordImportsFrom
import org.opentaint.ir.impl.python.protoToFlat.toPhysicalLocation
import org.opentaint.ir.impl.python.proto.MypyBlockProto
import org.opentaint.ir.impl.python.proto.MypyStmtProto

internal object CfgBuild {

    data class CfgBuildResult(
        val cfg: FlatCFG,
        val nonlocalNames: Set<String>,
        val globalNames: Set<String>,
    ) {
        companion object {
            val EMPTY = CfgBuildResult(FlatCFG.EMPTY, emptySet(), emptySet())
        }
    }

    fun buildFunctionCfg(
        module: ModuleContext,
        qualifiedName: String,
        functionName: String,
        body: MypyBlockProto,
        parameters: List<FlatParameter>,
        sourceLabel: String = qualifiedName,
        errorPrefix: String = "Failed to build CFG for $qualifiedName",
        imports: ImportManager = module.imports.nestedChild(),
        isConstructor: Boolean = false,
    ): CfgBuildResult {
        val constructorSelf = if (isConstructor) {
            parameters.firstOrNull()?.let { FlatLocal(it.name, it.type) }
        } else {
            null
        }

        val session = CfgSession(
            module = module,
            currentFunctionQualifiedName = qualifiedName,
            currentFunctionName = functionName,
            imports = imports,
            constructorSelf = constructorSelf,
        )
        return runOrEmpty(module, sourceLabel, errorPrefix) {
            for (param in parameters) {
                session.emit(
                    FlatAssign(
                        target = FlatLocal(param.name, param.type),
                        source = FlatParameterRef(param.name, param.type),
                    ),
                )
            }
            session.visitBlock(body)
            if (!session.currentBlockTerminated()) session.emitReturn(null)
            CfgBuildResult(session.finalizeCfg(), session.nonlocalNames, session.globalNames)
        }
    }

    fun buildModuleInitCfg(
        module: ModuleContext,
        statements: List<MypyStmtProto>,
    ): FlatCFG {
        val session = CfgSession(module = module)
        return runOrEmpty(
            module,
            sourceLabel = "__module_init__",
            errorPrefix = "Failed to build module_init CFG for ${module.moduleName}",
        ) {
            for (stmt in statements) {
                when {
                    stmt.hasImportStmt() -> recordImports(module.imports, stmt.importStmt)
                    stmt.hasImportFromStmt() -> recordImportsFrom(module.imports, stmt.importFromStmt)
                }
            }
            for (stmt in statements) {
                if (session.currentBlockTerminated()) break
                val location = stmt.toPhysicalLocation()
                when {
                    stmt.hasAssignment() -> session.visitAssignment(stmt.assignment, location)
                    stmt.hasImportStmt() || stmt.hasImportFromStmt() -> Unit
                    else -> module.reportError(
                        message = "buildModuleInitCfg: unexpected stmt kind ${stmt.kindCase} " +
                            "in MypyDefinitionProto.assignment slot",
                        source = "__module_init__",
                        code = "ModuleInitUnexpectedStmt",
                    )
                }
            }
            if (!session.currentBlockTerminated()) session.emitReturn(null)
            CfgBuildResult(session.finalizeCfg(), session.nonlocalNames, session.globalNames)
        }.cfg
    }

    private inline fun runOrEmpty(
        module: ModuleContext,
        sourceLabel: String,
        errorPrefix: String,
        block: () -> CfgBuildResult,
    ): CfgBuildResult = try {
        block()
    } catch (e: Exception) {
        module.reportException(errorPrefix, sourceLabel, e)
        CfgBuildResult.EMPTY
    }
}

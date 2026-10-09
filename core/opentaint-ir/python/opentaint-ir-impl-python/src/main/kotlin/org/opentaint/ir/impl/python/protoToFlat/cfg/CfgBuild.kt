package org.opentaint.ir.impl.python.protoToFlat.cfg

import org.opentaint.ir.impl.python.flat.FlatAssign
import org.opentaint.ir.impl.python.flat.FlatCFG
import org.opentaint.ir.impl.python.flat.FlatDeleteLocal
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatParameter
import org.opentaint.ir.impl.python.flat.FlatParameterRef
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.flat.mapOperand
import org.opentaint.ir.impl.python.flat.mapTarget
import org.opentaint.ir.impl.python.flat.targets
import org.opentaint.ir.impl.python.proto.MypyBlockProto
import org.opentaint.ir.impl.python.proto.MypyStmtProto
import org.opentaint.ir.impl.python.protoToFlat.ImportManager
import org.opentaint.ir.impl.python.protoToFlat.ModuleContext
import org.opentaint.ir.impl.python.protoToFlat.Scope
import org.opentaint.ir.impl.python.protoToFlat.recordImports
import org.opentaint.ir.impl.python.protoToFlat.recordImportsFrom
import org.opentaint.ir.impl.python.protoToFlat.toPhysicalLocation

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
            parameters.firstOrNull()?.let { FlatParameterRef(it.name, it.type) }
        } else {
            null
        }

        val session = CfgSession(
            module = module,
            scope = Scope(parameters),
            currentFunctionQualifiedName = qualifiedName,
            currentFunctionName = functionName,
            imports = imports,
            constructorSelf = constructorSelf,
        )
        return runOrEmpty(module, sourceLabel, errorPrefix) {
            session.visitBlock(body)
            if (!session.currentBlockTerminated()) session.emitReturn(null)
            CfgBuildResult(bindParameters(session.finalizeCfg(), parameters), session.nonlocalNames, session.globalNames)
        }
    }

    // Makes parameters immutable: a parameter the body writes is copied into a local at entry
    // and all its uses are renamed to that local; read-only parameters stay FlatParameterRef.
    private fun bindParameters(cfg: FlatCFG, parameters: List<FlatParameter>): FlatCFG {
        val written = writtenParameterNames(cfg)
        val copied = parameters.filter { it.name in written }
        if (copied.isEmpty()) return cfg

        val locals = copied.associate { it.name to FlatLocal(it.name, it.type) }
        val prologue = copied.map { FlatAssign(locals.getValue(it.name), FlatParameterRef(it.name, it.type)) }

        fun toLocal(v: FlatValue): FlatValue {
            if (v !is FlatParameterRef) return v

            return locals.getOrDefault(v.name, v)
        }

        val blocks = cfg.blocks.map { block ->
            val body = block.instructions.map { it.mapOperand(::toLocal).mapTarget(::toLocal) }
            block.copy(instructions = if (block.label == cfg.entryBlock) prologue + body else body)
        }
        return cfg.copy(blocks = blocks)
    }

    private fun writtenParameterNames(cfg: FlatCFG): Set<String> = buildSet {
        for (block in cfg.blocks) {
            for (inst in block.instructions) {
                for (target in inst.targets) if (target is FlatParameterRef) add(target.name)
                if (inst is FlatDeleteLocal) (inst.local as? FlatParameterRef)?.let { add(it.name) }
            }
        }
    }

    fun buildModuleInitCfg(
        module: ModuleContext,
        statements: List<MypyStmtProto>,
    ): FlatCFG {
        val session = CfgSession(module = module, scope = Scope(emptyList()))
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

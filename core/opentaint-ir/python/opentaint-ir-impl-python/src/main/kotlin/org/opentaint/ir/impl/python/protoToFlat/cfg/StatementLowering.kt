package org.opentaint.ir.impl.python.protoToFlat.cfg

import org.opentaint.ir.api.python.PIRPhysicalLocation
import org.opentaint.ir.impl.python.flat.FlatAnyType
import org.opentaint.ir.impl.python.flat.FlatAssign
import org.opentaint.ir.impl.python.flat.FlatBinOp
import org.opentaint.ir.impl.python.flat.FlatBinaryOperator
import org.opentaint.ir.impl.python.flat.FlatBindFunction
import org.opentaint.ir.impl.python.flat.FlatBoolConst
import org.opentaint.ir.impl.python.flat.FlatCall
import org.opentaint.ir.impl.python.flat.FlatCallArg
import org.opentaint.ir.impl.python.flat.FlatClassType
import org.opentaint.ir.impl.python.flat.FlatCompare
import org.opentaint.ir.impl.python.flat.FlatCompareOperator
import org.opentaint.ir.impl.python.flat.FlatDeleteAttr
import org.opentaint.ir.impl.python.flat.FlatDeleteLocal
import org.opentaint.ir.impl.python.flat.FlatDeleteSubscript
import org.opentaint.ir.impl.python.flat.FlatExceptHandler
import org.opentaint.ir.impl.python.flat.FlatGetIter
import org.opentaint.ir.impl.python.flat.FlatGlobalNameRef
import org.opentaint.ir.impl.python.flat.FlatLoadAttr
import org.opentaint.ir.impl.python.flat.FlatLocal
import org.opentaint.ir.impl.python.flat.FlatNextIter
import org.opentaint.ir.impl.python.flat.FlatNoneConst
import org.opentaint.ir.impl.python.flat.FlatRaise
import org.opentaint.ir.impl.python.flat.FlatReadName
import org.opentaint.ir.impl.python.flat.FlatStoreAttr
import org.opentaint.ir.impl.python.flat.FlatStoreSubscript
import org.opentaint.ir.impl.python.flat.FlatType
import org.opentaint.ir.impl.python.flat.FlatTypeCheck
import org.opentaint.ir.impl.python.flat.FlatUnpack
import org.opentaint.ir.impl.python.flat.FlatValue
import org.opentaint.ir.impl.python.proto.MypyAssertStmtProto
import org.opentaint.ir.impl.python.proto.MypyAssignmentStmtProto
import org.opentaint.ir.impl.python.proto.MypyBlockProto
import org.opentaint.ir.impl.python.proto.MypyDelStmtProto
import org.opentaint.ir.impl.python.proto.MypyExprProto
import org.opentaint.ir.impl.python.proto.MypyExpressionStmtProto
import org.opentaint.ir.impl.python.proto.MypyForStmtProto
import org.opentaint.ir.impl.python.proto.MypyFuncDefProto
import org.opentaint.ir.impl.python.proto.MypyIfStmtProto
import org.opentaint.ir.impl.python.proto.MypyMatchStmtProto
import org.opentaint.ir.impl.python.proto.MypyOperatorAssignmentStmtProto
import org.opentaint.ir.impl.python.proto.MypyPatternProto
import org.opentaint.ir.impl.python.proto.MypyRaiseStmtProto
import org.opentaint.ir.impl.python.proto.MypyReturnStmtProto
import org.opentaint.ir.impl.python.proto.MypySingletonPatternProto
import org.opentaint.ir.impl.python.proto.MypyStmtProto
import org.opentaint.ir.impl.python.proto.MypyTryStmtProto
import org.opentaint.ir.impl.python.proto.MypyWhileStmtProto
import org.opentaint.ir.impl.python.proto.MypyWithStmtProto
import org.opentaint.ir.impl.python.protoToFlat.DecoratorLowering
import org.opentaint.ir.impl.python.protoToFlat.FunctionLowering
import org.opentaint.ir.impl.python.protoToFlat.dottedPath
import org.opentaint.ir.impl.python.protoToFlat.qualify
import org.opentaint.ir.impl.python.protoToFlat.recordImports
import org.opentaint.ir.impl.python.protoToFlat.recordImportsFrom
import org.opentaint.ir.impl.python.protoToFlat.toPhysicalLocation

internal fun CfgSession.visitBlock(block: MypyBlockProto) {
    for (stmt in block.stmtsList) {
        if (currentBlockTerminated()) break
        visitStmt(stmt)
    }
}

private fun CfgSession.visitStmt(stmt: MypyStmtProto) {
    val loc = stmt.toPhysicalLocation()
    when {
        stmt.hasAssignment() -> visitAssignment(stmt.assignment, loc)
        stmt.hasOpAssignment() -> visitOperatorAssignment(stmt.opAssignment, loc)
        stmt.hasExpressionStmt() -> visitExpressionStmt(stmt.expressionStmt)
        stmt.hasReturnStmt() -> visitReturn(stmt.returnStmt, loc)
        stmt.hasIfStmt() -> visitIf(stmt.ifStmt, loc)
        stmt.hasWhileStmt() -> visitWhile(stmt.whileStmt, loc)
        stmt.hasForStmt() -> visitFor(stmt.forStmt, loc)
        stmt.hasMatchStmt() -> visitMatch(stmt.matchStmt, loc)
        stmt.hasTryStmt() -> visitTry(stmt.tryStmt, loc)
        stmt.hasWithStmt() -> visitWith(stmt.withStmt, loc)
        stmt.hasRaiseStmt() -> visitRaise(stmt.raiseStmt, loc)
        stmt.hasBreakStmt() -> breakTarget?.let { emitGoto(it) }
        stmt.hasContinueStmt() -> continueTarget?.let { emitGoto(it) }
        stmt.hasDelStmt() -> visitDel(stmt.delStmt, loc)
        stmt.hasAssertStmt() -> visitAssert(stmt.assertStmt, loc)
        stmt.hasFuncDef() -> visitNestedFuncDef(stmt.funcDef, emptyList(), loc)
        stmt.hasDecorator() ->
            visitNestedFuncDef(stmt.decorator.func, stmt.decorator.originalDecoratorsList, loc)
        stmt.hasGlobalDecl() -> recordGlobal(stmt.globalDecl.namesList)
        stmt.hasNonlocalDecl() -> recordNonlocal(stmt.nonlocalDecl.namesList)
        stmt.hasImportStmt() -> recordImports(imports, stmt.importStmt)
        stmt.hasImportFromStmt() -> recordImportsFrom(imports, stmt.importFromStmt)
    }
}

internal fun CfgSession.visitAssignment(stmt: MypyAssignmentStmtProto, location: PIRPhysicalLocation?) {
    if (!stmt.hasRvalue()) return
    val rhs = lowerExpr(stmt.rvalue)
    for (lvalue in stmt.lvaluesList) {
        assignTo(lvalue, rhs, location)
    }
}

internal fun CfgSession.assignTo(lvalue: MypyExprProto, rhs: FlatValue, location: PIRPhysicalLocation?) {
    when {
        lvalue.hasNameExpr() -> {
            val targetName = scope.resolveLocal(lvalue.nameExpr.name)
            emit(FlatAssign(FlatLocal(targetName), rhs, physicalLocation = location))
        }
        lvalue.hasMemberExpr() -> {
            val obj = lowerExpr(lvalue.memberExpr.expr)
            emit(FlatStoreAttr(obj, lvalue.memberExpr.name, rhs, physicalLocation = location))
        }
        lvalue.hasIndexExpr() -> {
            val obj = lowerExpr(lvalue.indexExpr.base)
            val index = lowerExpr(lvalue.indexExpr.index)
            emit(FlatStoreSubscript(obj, index, rhs, physicalLocation = location))
        }
        lvalue.hasTupleExpr() -> {
            val targets = mutableListOf<FlatValue>()
            var starIndex = -1
            for ((i, item) in lvalue.tupleExpr.itemsList.withIndex()) {
                when {
                    item.hasNameExpr() -> targets.add(FlatLocal(scope.resolveLocal(item.nameExpr.name)))
                    item.hasStarExpr() && item.starExpr.expr.hasNameExpr() -> {
                        targets.add(FlatLocal(scope.resolveLocal(item.starExpr.expr.nameExpr.name)))
                        starIndex = i
                    }
                    else -> targets.add(newTempValue())
                }
                if (item.hasStarExpr() && starIndex == -1) starIndex = i
            }
            emit(FlatUnpack(targets, rhs, starIndex, physicalLocation = location))
        }
        lvalue.hasStarExpr() -> assignTo(lvalue.starExpr.expr, rhs, location)
    }
}

private fun CfgSession.visitOperatorAssignment(stmt: MypyOperatorAssignmentStmtProto, location: PIRPhysicalLocation?) {
    val lhsVal = lowerExpr(stmt.lvalue)
    val rhsVal = lowerExpr(stmt.rvalue)
    val target = newTempValue()
    val op = BIN_OP_MAP[stmt.op] ?: FlatBinaryOperator.ADD
    emit(FlatBinOp(target, lhsVal, rhsVal, op, physicalLocation = location))
    assignTo(stmt.lvalue, target, location)
}

private fun CfgSession.visitExpressionStmt(stmt: MypyExpressionStmtProto) {
    lowerExpr(stmt.expr)
}

private fun CfgSession.visitReturn(stmt: MypyReturnStmtProto, location: PIRPhysicalLocation?) {
    val value = if (stmt.hasExpr() && stmt.expr.kindCase != MypyExprProto.KindCase.KIND_NOT_SET) {
        lowerExpr(stmt.expr)
    } else null
    emitReturn(value, location)
}

private fun CfgSession.visitIf(stmt: MypyIfStmtProto, location: PIRPhysicalLocation?) {
    val endBlock = newBlock()

    for (i in stmt.conditionsList.indices) {
        val condition = stmt.getConditions(i)
        val condVal = lowerExpr(condition)
        val trueBlock = newBlock()
        val falseBlock = if (i < stmt.conditionsCount - 1 || stmt.hasElseBody()) newBlock() else endBlock

        emitBranch(condVal, trueBlock, falseBlock, condition.toPhysicalLocation() ?: location)

        activate(trueBlock)
        visitBlock(stmt.getBodies(i))
        emitGotoIfOpen(endBlock)

        if (falseBlock != endBlock) activate(falseBlock)
    }

    if (stmt.hasElseBody()) {
        visitBlock(stmt.elseBody)
        emitGotoIfOpen(endBlock)
    }

    activate(endBlock)
}

private fun CfgSession.visitMatch(stmt: MypyMatchStmtProto, location: PIRPhysicalLocation?) {
    val subject = lowerExpr(stmt.subject)
    val endBlock = newBlock()

    if (stmt.patternsCount == 0) emitGoto(endBlock)

    for (i in 0 until stmt.patternsCount) {
        val pattern = stmt.getPatterns(i)
        val guard = stmt.getGuards(i)
        val hasGuard = guard.kindCase != MypyExprProto.KindCase.KIND_NOT_SET
        val nextBlock = if (i < stmt.patternsCount - 1) newBlock() else endBlock

        val matchedBlock = newBlock()
        emitPatternTest(pattern, subject, matchedBlock, nextBlock, location)

        activate(matchedBlock)
        if (hasGuard) {
            val guardVal = lowerExpr(guard)
            val bodyBlock = newBlock()
            emitBranch(guardVal, bodyBlock, nextBlock, location)
            activate(bodyBlock)
        }
        visitBlock(stmt.getBodies(i))
        emitGotoIfOpen(endBlock)

        if (nextBlock != endBlock) activate(nextBlock)
    }

    activate(endBlock)
}

private fun CfgSession.emitPatternTest(
    pattern: MypyPatternProto,
    subject: FlatValue,
    matchBlock: Int,
    failBlock: Int,
    location: PIRPhysicalLocation?,
) {
    // todo: support complex patterns
    when {
        pattern.hasAsPattern() -> {
            val asPattern = pattern.asPattern
            val bindBlock = if (asPattern.name.isNotEmpty()) newBlock() else matchBlock
            if (asPattern.hasPattern()) emitPatternTest(asPattern.pattern, subject, bindBlock, failBlock, location)
            else emitGoto(bindBlock)
            if (bindBlock != matchBlock) {
                activate(bindBlock)
                emit(FlatAssign(FlatLocal(scope.resolveLocal(asPattern.name)), subject, physicalLocation = location))
                emitGoto(matchBlock)
            }
        }
        pattern.hasValuePattern() -> {
            val rhs = lowerExpr(pattern.valuePattern.expr)
            emitCompareBranch(subject, rhs, FlatCompareOperator.EQ, matchBlock, failBlock, location)
        }
        pattern.hasSingletonPattern() -> {
            val rhs = when (pattern.singletonPattern.value) {
                MypySingletonPatternProto.Value.TRUE -> FlatBoolConst(true)
                MypySingletonPatternProto.Value.FALSE -> FlatBoolConst(false)
                else -> FlatNoneConst
            }
            emitCompareBranch(subject, rhs, FlatCompareOperator.IS, matchBlock, failBlock, location)
        }
        pattern.hasOrPattern() -> {
            val alternatives = pattern.orPattern.patternsList
            if (alternatives.isEmpty()) {
                emitGoto(failBlock)
                return
            }
            for ((index, alternative) in alternatives.withIndex()) {
                val nextAlternative = if (index < alternatives.size - 1) newBlock() else failBlock
                emitPatternTest(alternative, subject, matchBlock, nextAlternative, location)
                if (nextAlternative != failBlock) activate(nextAlternative)
            }
        }
        pattern.hasClassPattern() -> {
            val typeMatched = newTempValue()
            emit(FlatTypeCheck(typeMatched, subject, resolveClassType(pattern.classPattern.classRef), physicalLocation = location))
            emitBranch(typeMatched, matchBlock, failBlock, location)
        }
        pattern.hasUnknownPattern() -> {
            module.reportWarning(
                "unsupported match pattern ${pattern.unknownPattern.kind}; bindings dropped",
                currentFunctionQualifiedName ?: module.moduleName,
                "UnsupportedMatchPattern",
            )
            emitOpaqueTest(subject, matchBlock, failBlock, location)
        }
        else -> emitGoto(matchBlock)
    }
}

private fun CfgSession.emitOpaqueTest(
    subject: FlatValue,
    matchBlock: Int,
    failBlock: Int,
    location: PIRPhysicalLocation?,
) {
    val target = newTempValue()
    emit(FlatTypeCheck(target, subject, FlatAnyType, physicalLocation = location))
    emitBranch(target, matchBlock, failBlock, location)
}

private fun CfgSession.emitCompareBranch(
    left: FlatValue,
    right: FlatValue,
    op: FlatCompareOperator,
    matchBlock: Int,
    failBlock: Int,
    location: PIRPhysicalLocation?,
) {
    val target = newTempValue()
    emit(FlatCompare(target, left, right, op, physicalLocation = location))
    emitBranch(target, matchBlock, failBlock, location)
}

private fun CfgSession.resolveClassType(classRef: MypyExprProto): FlatType = when {
    classRef.hasNameExpr() ->
        FlatClassType(imports.qualify(classRef.nameExpr) ?: "builtins.${classRef.nameExpr.name}")
    classRef.hasMemberExpr() -> FlatClassType(imports.dottedPath(classRef.memberExpr))
    else -> FlatAnyType
}

private fun CfgSession.visitWhile(stmt: MypyWhileStmtProto, location: PIRPhysicalLocation?) {
    val headerBlock = newBlock()
    val bodyBlock = newBlock()
    val hasElseBody = stmt.hasElseBody() && stmt.elseBody.stmtsCount > 0

    val elseBlock: Int?
    val exitBlock: Int
    val breakBlock: Int
    if (hasElseBody) {
        elseBlock = newBlock()
        breakBlock = newBlock()
        exitBlock = elseBlock
    } else {
        elseBlock = null
        exitBlock = newBlock()
        breakBlock = exitBlock
    }

    emitGoto(headerBlock)
    activate(headerBlock)

    val cond = lowerExpr(stmt.condition)
    emitBranch(cond, bodyBlock, exitBlock, location)

    activate(bodyBlock)
    withLoopTargets(breakBlock = breakBlock, continueBlock = headerBlock) {
        visitBlock(stmt.body)
    }
    emitGotoIfOpen(headerBlock)

    if (elseBlock != null) {
        activate(elseBlock)
        visitBlock(stmt.elseBody)
        emitGotoIfOpen(breakBlock)
        activate(breakBlock)
    } else {
        activate(exitBlock)
    }
}

private fun CfgSession.visitFor(stmt: MypyForStmtProto, location: PIRPhysicalLocation?) {
    val iterVal = newTempValue()
    val iterableVal = lowerExpr(stmt.iterable)
    emit(FlatGetIter(iterVal, iterableVal, physicalLocation = location))

    val headerBlock = newBlock()
    val bodyBlock = newBlock()
    val hasElseBody = stmt.hasElseBody() && stmt.elseBody.stmtsCount > 0

    val elseBlock: Int?
    val exitBlock: Int
    val breakBlock: Int
    if (hasElseBody) {
        elseBlock = newBlock()
        breakBlock = newBlock()
        exitBlock = elseBlock
    } else {
        elseBlock = null
        exitBlock = newBlock()
        breakBlock = exitBlock
    }

    emitGoto(headerBlock)
    activate(headerBlock)

    val targetVal = lowerForTarget(stmt.index)
    emit(FlatNextIter(targetVal, iterVal, bodyBlock, exitBlock, physicalLocation = location))

    activate(bodyBlock)
    if (stmt.index.hasTupleExpr()) {
        assignTo(stmt.index, targetVal, location)
    }
    withLoopTargets(breakBlock = breakBlock, continueBlock = headerBlock) {
        visitBlock(stmt.body)
    }
    emitGotoIfOpen(headerBlock)

    if (elseBlock != null) {
        activate(elseBlock)
        visitBlock(stmt.elseBody)
        emitGotoIfOpen(breakBlock)
        activate(breakBlock)
    } else {
        activate(exitBlock)
    }
}

private fun CfgSession.lowerForTarget(target: MypyExprProto): FlatLocal = when {
    target.hasNameExpr() -> FlatLocal(scope.resolveLocal(target.nameExpr.name))
    else -> newTempValue()
}

private fun CfgSession.visitTry(stmt: MypyTryStmtProto, location: PIRPhysicalLocation?) {
    val handlerBlocks = (0 until stmt.handlersCount).map { newBlock() }
    val finallyBlock = if (stmt.hasFinallyBody() && stmt.finallyBody.stmtsCount > 0) newBlock() else null
    val elseBlock = if (stmt.hasElseBody() && stmt.elseBody.stmtsCount > 0) newBlock() else null
    val endBlock = newBlock()

    val tryBodyBlock = newBlock()
    emitGoto(tryBodyBlock)
    activate(tryBodyBlock)

    withExceptionHandlers(handlerBlocks) {
        visitBlock(stmt.body)

        emitGotoIfOpen(elseBlock ?: finallyBlock ?: endBlock)

        closeCurrentBlock()
    }

    for (i in 0 until stmt.handlersCount) {
        activate(handlerBlocks[i])

        val excTypes = if (i < stmt.typesCount && stmt.getTypes(i).kindCase != MypyExprProto.KindCase.KIND_NOT_SET) {
            resolveExceptTypes(stmt.getTypes(i))
        } else emptyList()

        val excTarget = if (i < stmt.varsCount && stmt.getVars(i).hasNameExpr()) {
            FlatLocal(scope.resolveLocal(stmt.getVars(i).nameExpr.name))
        } else null

        emit(FlatExceptHandler(excTarget, excTypes, physicalLocation = location))

        visitBlock(stmt.getHandlers(i))
        emitGotoIfOpen(finallyBlock ?: endBlock)
    }

    if (elseBlock != null) {
        activate(elseBlock)
        visitBlock(stmt.elseBody)
        emitGotoIfOpen(finallyBlock ?: endBlock)
    }

    if (finallyBlock != null) {
        activate(finallyBlock)
        visitBlock(stmt.finallyBody)
        emitGotoIfOpen(endBlock)
    }

    activate(endBlock)
}

private fun CfgSession.resolveExceptTypes(typeExpr: MypyExprProto): List<FlatType> {
    val result = mutableListOf<FlatType>()
    when {
        typeExpr.hasTupleExpr() -> {
            for (item in typeExpr.tupleExpr.itemsList) result.addAll(resolveExceptTypes(item))
        }
        typeExpr.hasNameExpr() -> {
            val ne = typeExpr.nameExpr
            result.add(FlatClassType(imports.qualify(ne) ?: "builtins.${ne.name}"))
        }
        typeExpr.hasMemberExpr() -> {
            result.add(FlatClassType(imports.dottedPath(typeExpr.memberExpr)))
        }
        else -> result.add(FlatClassType("builtins.Exception"))
    }
    return result
}

private fun CfgSession.visitWith(stmt: MypyWithStmtProto, location: PIRPhysicalLocation?) {
    val ctxVals = mutableListOf<FlatValue>()
    for (i in stmt.exprsList.indices) {
        val ctxVal = lowerExpr(stmt.getExprs(i))
        ctxVals.add(ctxVal)

        val enterAttr = newTempValue()
        emit(FlatLoadAttr(enterAttr, ctxVal, "__enter__", physicalLocation = location))
        val enterResult = newTempValue()
        emit(FlatCall(enterResult, enterAttr, physicalLocation = location))
        if (i < stmt.targetsCount) {
            val target = stmt.getTargets(i)
            if (target.kindCase != MypyExprProto.KindCase.KIND_NOT_SET) {
                assignTo(target, enterResult, location)
            }
        }
    }

    visitBlock(stmt.body)

    if (currentBlockTerminated()) return

    val noneArg = FlatCallArg(FlatNoneConst)
    for (ctxVal in ctxVals.reversed()) {
        val exitAttr = newTempValue()
        emit(FlatLoadAttr(exitAttr, ctxVal, "__exit__", physicalLocation = location))
        val exitResult = newTempValue()
        emit(FlatCall(exitResult, exitAttr, listOf(noneArg, noneArg, noneArg), physicalLocation = location))
    }
}

private fun CfgSession.visitRaise(stmt: MypyRaiseStmtProto, location: PIRPhysicalLocation?) {
    val exc = if (stmt.hasExpr() && stmt.expr.kindCase != MypyExprProto.KindCase.KIND_NOT_SET) {
        lowerExpr(stmt.expr)
    } else null
    val cause = if (stmt.hasFromExpr() && stmt.fromExpr.kindCase != MypyExprProto.KindCase.KIND_NOT_SET) {
        lowerExpr(stmt.fromExpr)
    } else null
    emit(FlatRaise(exc, cause, physicalLocation = location))
}

private fun CfgSession.visitDel(stmt: MypyDelStmtProto, location: PIRPhysicalLocation?) =
    visitDelExpr(stmt.expr, location)

private fun CfgSession.visitDelExpr(expr: MypyExprProto, location: PIRPhysicalLocation?) {
    when {
        expr.hasNameExpr() ->
            emit(FlatDeleteLocal(FlatLocal(scope.resolveLocal(expr.nameExpr.name)), physicalLocation = location))
        expr.hasMemberExpr() -> {
            val obj = lowerExpr(expr.memberExpr.expr)
            emit(FlatDeleteAttr(obj, expr.memberExpr.name, physicalLocation = location))
        }
        expr.hasIndexExpr() -> {
            val obj = lowerExpr(expr.indexExpr.base)
            val index = lowerExpr(expr.indexExpr.index)
            emit(FlatDeleteSubscript(obj, index, physicalLocation = location))
        }
        expr.hasTupleExpr() -> for (item in expr.tupleExpr.itemsList) visitDelExpr(item, location)
    }
}

private fun CfgSession.visitAssert(stmt: MypyAssertStmtProto, location: PIRPhysicalLocation?) {
    val cond = lowerExpr(stmt.expr)
    val passBlock = newBlock()
    val failBlock = newBlock()
    emitBranch(cond, passBlock, failBlock, location)

    activate(failBlock)
    val excClass = newTempValue()
    emit(FlatReadName(excClass, FlatGlobalNameRef("builtins.AssertionError"), physicalLocation = location))
    var exc: FlatValue = excClass
    if (stmt.hasMsg() && stmt.msg.kindCase != MypyExprProto.KindCase.KIND_NOT_SET) {
        val msgVal = lowerExpr(stmt.msg)
        val callTarget = newTempValue()
        emit(FlatCall(callTarget, exc, listOf(FlatCallArg(msgVal)), physicalLocation = location))
        exc = callTarget
    }
    emit(FlatRaise(exc, null, physicalLocation = location))

    activate(passBlock)
}

private fun CfgSession.visitNestedFuncDef(
    funcDef: MypyFuncDefProto,
    decoratorExprs: List<MypyExprProto>,
    location: PIRPhysicalLocation?,
) {
    val decorators = decoratorExprs.map { DecoratorLowering.fromExpr(it, imports) }

    val enclosing = requireNotNull(currentFunctionQualifiedName) {
        "visitNestedFuncDef invoked outside a function scope"
    }
    val enclosingFnName = requireNotNull(currentFunctionName) {
        "visitNestedFuncDef invoked outside a function scope (no currentFunctionName)"
    }
    val nested = FunctionLowering.lowerNestedFunction(
        module = module,
        funcDef = funcDef,
        decorators = decorators,
        enclosingQualifiedName = enclosing,
        enclosingName = enclosingFnName,
        enclosingImports = imports,
    )
    module.register(nested)

    val ref = FlatGlobalNameRef(nested.qualifiedName)
    val targetName = scope.resolveLocal(funcDef.name)
    emit(FlatBindFunction(FlatLocal(targetName), ref, physicalLocation = location))
}

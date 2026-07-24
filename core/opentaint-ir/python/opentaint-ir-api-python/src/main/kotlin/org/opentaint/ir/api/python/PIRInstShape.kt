package org.opentaint.ir.api.python

val PIRInstruction.targets: List<PIRLocalVar>
    get() = accept(TargetExtractor)

private object TargetExtractor : PIRInstVisitor<List<PIRLocalVar>> {
    override fun visitAssign(inst: PIRAssign)                   = listOf(inst.target)
    override fun visitLoadAttr(inst: PIRLoadAttr)               = listOf(inst.target)
    override fun visitStoreAttr(inst: PIRStoreAttr)             = emptyList<PIRLocalVar>()
    override fun visitStoreSubscript(inst: PIRStoreSubscript)   = emptyList<PIRLocalVar>()
    override fun visitStoreGlobal(inst: PIRStoreGlobal)         = emptyList<PIRLocalVar>()
    override fun visitStoreClosure(inst: PIRStoreClosure)       = emptyList<PIRLocalVar>()
    override fun visitCall(inst: PIRCall)                       = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitNextIter(inst: PIRNextIter)               = listOf(inst.target)
    override fun visitUnpack(inst: PIRUnpack)                   = inst.targets
    override fun visitGoto(inst: PIRGoto)                       = emptyList<PIRLocalVar>()
    override fun visitBranch(inst: PIRBranch)                   = emptyList<PIRLocalVar>()
    override fun visitReturn(inst: PIRReturn)                   = emptyList<PIRLocalVar>()
    override fun visitRaise(inst: PIRRaise)                     = emptyList<PIRLocalVar>()
    override fun visitExceptHandler(inst: PIRExceptHandler)     = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitYield(inst: PIRYield)                     = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitYieldFrom(inst: PIRYieldFrom)             = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitAwait(inst: PIRAwait)                     = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitDeleteLocal(inst: PIRDeleteLocal)         = emptyList<PIRLocalVar>()
    override fun visitDeleteAttr(inst: PIRDeleteAttr)           = emptyList<PIRLocalVar>()
    override fun visitDeleteSubscript(inst: PIRDeleteSubscript) = emptyList<PIRLocalVar>()
    override fun visitDeleteGlobal(inst: PIRDeleteGlobal)       = emptyList<PIRLocalVar>()
    override fun visitUnreachable(inst: PIRUnreachable)         = emptyList<PIRLocalVar>()
}

val PIRInstruction.operands: List<PIRValue>
    get() = accept(OperandExtractor)

val PIRInstruction.locals: List<PIRLocalVar>
    get() = operands.filterIsInstance<PIRLocalVar>()

private object OperandExtractor : PIRInstVisitor<List<PIRValue>> {
    override fun visitAssign(inst: PIRAssign)                   = listOf<PIRValue>(inst.target) + inst.expr.operands()
    override fun visitLoadAttr(inst: PIRLoadAttr)               = listOf(inst.target, inst.obj)
    override fun visitStoreAttr(inst: PIRStoreAttr)             = listOf(inst.obj, inst.value)
    override fun visitStoreSubscript(inst: PIRStoreSubscript)   = listOf(inst.obj, inst.index, inst.value)
    override fun visitStoreGlobal(inst: PIRStoreGlobal)         = listOf(inst.value)
    override fun visitStoreClosure(inst: PIRStoreClosure)       = listOf(inst.value)
    override fun visitCall(inst: PIRCall)                       = inst.target?.let { listOf<PIRValue>(it) }.orEmpty() +
                                                                      inst.callee + inst.args.map { it.value }
    override fun visitNextIter(inst: PIRNextIter)               = listOf(inst.target, inst.iterator)
    override fun visitUnpack(inst: PIRUnpack)                   = inst.targets + inst.source
    override fun visitGoto(inst: PIRGoto)                       = emptyList<PIRValue>()
    override fun visitBranch(inst: PIRBranch)                   = listOf(inst.condition)
    override fun visitReturn(inst: PIRReturn)                   = listOfNotNull(inst.value)
    override fun visitRaise(inst: PIRRaise)                     = listOfNotNull(inst.exception, inst.cause)
    override fun visitExceptHandler(inst: PIRExceptHandler)     = listOfNotNull(inst.target)
    override fun visitYield(inst: PIRYield)                     = listOfNotNull(inst.target, inst.value)
    override fun visitYieldFrom(inst: PIRYieldFrom)             = listOfNotNull<PIRValue>(inst.target) + inst.iterable
    override fun visitAwait(inst: PIRAwait)                     = listOfNotNull<PIRValue>(inst.target) + inst.awaitable
    override fun visitDeleteLocal(inst: PIRDeleteLocal)         = listOf(inst.local)
    override fun visitDeleteAttr(inst: PIRDeleteAttr)           = listOf(inst.obj)
    override fun visitDeleteSubscript(inst: PIRDeleteSubscript) = listOf(inst.obj, inst.index)
    // `ref` is a structural name reference, not a value read.
    override fun visitDeleteGlobal(inst: PIRDeleteGlobal)       = emptyList<PIRValue>()
    override fun visitUnreachable(inst: PIRUnreachable)         = emptyList<PIRValue>()
}

private fun PIRExpr.operands(): List<PIRValue> = when (this) {
    is PIRValue           -> listOf(this)
    is PIRBinaryExpr      -> listOf(left, right)
    is PIRCompareExpr     -> listOf(left, right)
    is PIRUnaryExpr       -> listOf(operand)
    is PIRSubscriptExpr   -> listOf(obj, index)
    is PIRListExpr        -> elements
    is PIRTupleExpr       -> elements
    is PIRSetExpr         -> elements
    is PIRDictExpr        -> keys + values
    is PIRSliceExpr       -> listOfNotNull(obj, lower, upper, step)
    is PIRStringExpr      -> parts
    is PIRIterExpr        -> listOf(iterable)
    is PIRTypeCheckExpr   -> listOf(value)
    // Structural name references, not value reads.
    is PIRBindFunctionExpr -> emptyList()
    is PIRReadNameExpr     -> emptyList()
}

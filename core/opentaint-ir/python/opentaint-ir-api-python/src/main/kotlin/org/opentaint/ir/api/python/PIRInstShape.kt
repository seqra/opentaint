package org.opentaint.ir.api.python

/**
 * Shape utilities for [PIRInstruction]: the result-target slot.
 * Mirrors [FlatInstShape] for the PIR layer.
 *
 * Note: write-side mappers (`mapTarget`, `mapOperand`) are intentionally absent.
 * PIR instructions use identity-based equality and their [PIRLocation] must not
 * be aliased across copies — structural `copy()` would silently corrupt the IR.
 * See the [PIRInstruction] KDoc for details.
 *
 * Conventions
 * -----------
 *
 * **Targets.** "Target" means the [PIRValue] slot that the instruction *writes*
 * to (the result slot).
 * - Most instructions have exactly one target.
 * - [PIRCall], [PIRExceptHandler], [PIRYield], [PIRYieldFrom], [PIRAwait] have a
 *   nullable target: [targets] returns an empty list when the result is discarded.
 * - [PIRUnpack] has multiple targets (one per unpacked element slot).
 * - Side-effect-only instructions ([PIRStoreAttr], [PIRStoreSubscript],
 *   [PIRStoreGlobal], [PIRStoreClosure], control-flow terminators, and deletes)
 *   produce no target — [targets] returns an empty list.
 */

/**
 * The write targets of this instruction — the [PIRValue] slots that receive a
 * result. Empty for side-effect-only and control-flow instructions.
 */
val PIRInstruction.targets: List<PIRValue>
    get() = accept(TargetExtractor)

private object TargetExtractor : PIRInstVisitor<List<PIRValue>> {
    override fun visitAssign(inst: PIRAssign)                   = listOf(inst.target)
    override fun visitLoadAttr(inst: PIRLoadAttr)               = listOf(inst.target)
    override fun visitStoreAttr(inst: PIRStoreAttr)             = emptyList<PIRValue>()
    override fun visitStoreSubscript(inst: PIRStoreSubscript)   = emptyList<PIRValue>()
    override fun visitStoreGlobal(inst: PIRStoreGlobal)         = emptyList<PIRValue>()
    override fun visitStoreClosure(inst: PIRStoreClosure)       = emptyList<PIRValue>()
    override fun visitCall(inst: PIRCall)                       = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitNextIter(inst: PIRNextIter)               = listOf(inst.target)
    override fun visitUnpack(inst: PIRUnpack)                   = inst.targets
    override fun visitGoto(inst: PIRGoto)                       = emptyList<PIRValue>()
    override fun visitBranch(inst: PIRBranch)                   = emptyList<PIRValue>()
    override fun visitReturn(inst: PIRReturn)                   = emptyList<PIRValue>()
    override fun visitRaise(inst: PIRRaise)                     = emptyList<PIRValue>()
    override fun visitExceptHandler(inst: PIRExceptHandler)     = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitYield(inst: PIRYield)                     = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitYieldFrom(inst: PIRYieldFrom)             = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitAwait(inst: PIRAwait)                     = inst.target?.let { listOf(it) }.orEmpty()
    override fun visitDeleteLocal(inst: PIRDeleteLocal)         = emptyList<PIRValue>()
    override fun visitDeleteAttr(inst: PIRDeleteAttr)           = emptyList<PIRValue>()
    override fun visitDeleteSubscript(inst: PIRDeleteSubscript) = emptyList<PIRValue>()
    override fun visitDeleteGlobal(inst: PIRDeleteGlobal)       = emptyList<PIRValue>()
    override fun visitUnreachable(inst: PIRUnreachable)         = emptyList<PIRValue>()
}

package org.opentaint.jvm.graph

import org.opentaint.ir.api.jvm.cfg.AbstractJIRInst
import org.opentaint.ir.api.jvm.cfg.JIRBranchingInst
import org.opentaint.ir.api.jvm.cfg.JIRExpr
import org.opentaint.ir.api.jvm.cfg.JIRInstLocation
import org.opentaint.ir.api.jvm.cfg.JIRInstRef
import org.opentaint.ir.api.jvm.cfg.JIRInstVisitor

sealed interface JMethodBoundaryInst : JIRBranchingInst

class JMethodEnterInst(location: JIRInstLocation) : AbstractJIRInst(location), JMethodBoundaryInst {
    override val operands: List<JIRExpr> get() = emptyList()
    override val successors: List<JIRInstRef> get() = emptyList()

    override fun toString(): String = "method enter"

    override fun <T> accept(visitor: JIRInstVisitor<T>): T = visitor.visitExternalJIRInst(this)
}

class JMethodExitNormalInst(location: JIRInstLocation) : AbstractJIRInst(location), JMethodBoundaryInst {
    override val operands: List<JIRExpr> get() = emptyList()
    override val successors: List<JIRInstRef> get() = emptyList()

    override fun toString(): String = "method exit"

    override fun <T> accept(visitor: JIRInstVisitor<T>): T = visitor.visitExternalJIRInst(this)
}

class JMethodExitExceptionalInst(location: JIRInstLocation) : AbstractJIRInst(location), JMethodBoundaryInst {
    override val operands: List<JIRExpr> get() = emptyList()
    override val successors: List<JIRInstRef> get() = emptyList()

    override fun toString(): String = "method exit (exceptional)"

    override fun <T> accept(visitor: JIRInstVisitor<T>): T = visitor.visitExternalJIRInst(this)
}

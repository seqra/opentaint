package org.opentaint.dataflow.jvm.bidi.interp

import org.opentaint.dataflow.graph.LocalAccess
import org.opentaint.ir.api.jvm.cfg.*
import java.util.BitSet

/** Raw instruction operands only. This function cannot load rules or aliases. */
internal fun localAccess(instruction: JIRInst): LocalAccess {
    fun locals(expression: JIRExpr, into: BitSet) {
        if (expression is JIRLocalVar) into.set(expression.index)
        expression.operands.forEach { locals(it, into) }
    }
    val uses = BitSet(); val definitions = BitSet(); val mentions = BitSet()
    instruction.operands.forEach { locals(it, mentions) }
    if (instruction is JIRAssignInst) {
        locals(instruction.rhv, uses)
        val lhs = instruction.lhv as? JIRLocalVar
        if (lhs != null) {
            // Only a plain copy is certified nonthrowing. False from the
            // language's exceptional-control query is not such a certificate.
            if (instruction.rhv is JIRImmediate) definitions.set(lhs.index)
        } else locals(instruction.lhv, uses)
    } else uses.or(mentions)
    return LocalAccess(uses, definitions, mentions)
}

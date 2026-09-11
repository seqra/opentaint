package org.opentaint.ir.impl.python.flatToPir

import org.opentaint.ir.api.python.PIRBoolConst
import org.opentaint.ir.api.python.PIRBytesConst
import org.opentaint.ir.api.python.PIRComplexConst
import org.opentaint.ir.api.python.PIREllipsisConst
import org.opentaint.ir.api.python.PIRFloatConst
import org.opentaint.ir.api.python.PIRIntConst
import org.opentaint.ir.api.python.PIRNoneConst
import org.opentaint.ir.api.python.PIRStrConst
import org.opentaint.ir.api.python.PIRValue
import org.opentaint.ir.impl.python.flat.FlatBoolConst
import org.opentaint.ir.impl.python.flat.FlatBytesConst
import org.opentaint.ir.impl.python.flat.FlatComplexConst
import org.opentaint.ir.impl.python.flat.FlatConst
import org.opentaint.ir.impl.python.flat.FlatEllipsisConst
import org.opentaint.ir.impl.python.flat.FlatFloatConst
import org.opentaint.ir.impl.python.flat.FlatIntConst
import org.opentaint.ir.impl.python.flat.FlatNoneConst
import org.opentaint.ir.impl.python.flat.FlatStrConst

object ConstConverter {
    fun convert(c: FlatConst): PIRValue = when (c) {
        is FlatIntConst -> PIRIntConst(c.value)
        is FlatFloatConst -> PIRFloatConst(c.value)
        is FlatStrConst -> PIRStrConst(c.value)
        is FlatBoolConst -> PIRBoolConst(c.value)
        is FlatNoneConst -> PIRNoneConst
        is FlatEllipsisConst -> PIREllipsisConst
        is FlatBytesConst -> PIRBytesConst(c.value)
        is FlatComplexConst -> PIRComplexConst(c.real, c.imag)
    }
}

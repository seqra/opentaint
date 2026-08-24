package org.opentaint.ir.impl.python.protoToFlat

import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.proto.MypyModuleProto

object ProtoToFlat {
    fun lowerModule(astModule: MypyModuleProto): FlatModuleIR =
        ModuleLowering.lower(astModule)
}

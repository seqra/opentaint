package org.opentaint.ir.test.python.protoToFlat

import org.opentaint.ir.api.python.PIRSettings
import org.opentaint.ir.impl.python.PIRServerConnection
import org.opentaint.ir.impl.python.flat.FlatModuleIR
import org.opentaint.ir.impl.python.protoToFlat.ProtoToFlat
import org.opentaint.ir.impl.python.toBuildProjectRequest

object PIRRawFlatLoader {
    fun loadRawFlatModules(settings: PIRSettings): List<FlatModuleIR> =
        PIRServerConnection.open(settings).use { connection ->
            connection.buildProject(settings.toBuildProjectRequest()) { iterator ->
                val result = mutableListOf<FlatModuleIR>()
                while (iterator.hasNext()) {
                    val astModuleProto = iterator.next()
                    if (astModuleProto.errorsCount > 0) continue
                    result.add(ProtoToFlat.lowerModule(astModuleProto))
                }
                result
            }
        }
}

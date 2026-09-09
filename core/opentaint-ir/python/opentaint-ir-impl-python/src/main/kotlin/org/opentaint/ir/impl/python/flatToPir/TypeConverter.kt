package org.opentaint.ir.impl.python.flatToPir

import org.opentaint.ir.api.python.PIRAnyType
import org.opentaint.ir.api.python.PIRClassType
import org.opentaint.ir.api.python.PIRFunctionType
import org.opentaint.ir.api.python.PIRLiteralType
import org.opentaint.ir.api.python.PIRNeverType
import org.opentaint.ir.api.python.PIRNoneType
import org.opentaint.ir.api.python.PIRTupleType
import org.opentaint.ir.api.python.PIRType
import org.opentaint.ir.api.python.PIRTypeVarType
import org.opentaint.ir.api.python.PIRUnionType
import org.opentaint.ir.impl.python.flat.FlatAnyType
import org.opentaint.ir.impl.python.flat.FlatClassType
import org.opentaint.ir.impl.python.flat.FlatFunctionType
import org.opentaint.ir.impl.python.flat.FlatLiteralType
import org.opentaint.ir.impl.python.flat.FlatNeverType
import org.opentaint.ir.impl.python.flat.FlatNoneType
import org.opentaint.ir.impl.python.flat.FlatTupleType
import org.opentaint.ir.impl.python.flat.FlatType
import org.opentaint.ir.impl.python.flat.FlatTypeVarType
import org.opentaint.ir.impl.python.flat.FlatUnionType

object TypeConverter {
    fun convert(flat: FlatType): PIRType = when (flat) {
        is FlatAnyType -> PIRAnyType
        is FlatNeverType -> PIRNeverType
        is FlatNoneType -> PIRNoneType
        is FlatClassType -> PIRClassType(
            qualifiedName = flat.qualifiedName,
            typeArgs = flat.typeArgs.map { convert(it) },
        )
        is FlatFunctionType -> PIRFunctionType(
            paramTypes = flat.paramTypes.map { convert(it) },
            returnType = convert(flat.returnType),
        )
        is FlatUnionType -> PIRUnionType(members = flat.members.map { convert(it) })
        is FlatTupleType -> PIRTupleType(
            elementTypes = flat.elementTypes.map { convert(it) },
            isVarLength = flat.isVarLength,
        )
        is FlatLiteralType -> PIRLiteralType(
            value = flat.value,
            baseType = convert(flat.baseType),
        )
        is FlatTypeVarType -> PIRTypeVarType(
            name = flat.name,
            bounds = flat.bounds.map { convert(it) },
        )
    }
}

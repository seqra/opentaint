package org.opentaint.ir.impl.python.flatToPir

import org.opentaint.ir.api.python.PIRAddExpr
import org.opentaint.ir.api.python.PIRBinaryExpr
import org.opentaint.ir.api.python.PIRBitAndExpr
import org.opentaint.ir.api.python.PIRBitOrExpr
import org.opentaint.ir.api.python.PIRBitXorExpr
import org.opentaint.ir.api.python.PIRCallArgKind
import org.opentaint.ir.api.python.PIRCompareExpr
import org.opentaint.ir.api.python.PIRDivExpr
import org.opentaint.ir.api.python.PIREqExpr
import org.opentaint.ir.api.python.PIRFloorDivExpr
import org.opentaint.ir.api.python.PIRGeExpr
import org.opentaint.ir.api.python.PIRGtExpr
import org.opentaint.ir.api.python.PIRInExpr
import org.opentaint.ir.api.python.PIRInvertExpr
import org.opentaint.ir.api.python.PIRIsExpr
import org.opentaint.ir.api.python.PIRIsNotExpr
import org.opentaint.ir.api.python.PIRLShiftExpr
import org.opentaint.ir.api.python.PIRLeExpr
import org.opentaint.ir.api.python.PIRLtExpr
import org.opentaint.ir.api.python.PIRMatMulExpr
import org.opentaint.ir.api.python.PIRModExpr
import org.opentaint.ir.api.python.PIRMulExpr
import org.opentaint.ir.api.python.PIRNeExpr
import org.opentaint.ir.api.python.PIRNegExpr
import org.opentaint.ir.api.python.PIRNotExpr
import org.opentaint.ir.api.python.PIRNotInExpr
import org.opentaint.ir.api.python.PIRParameterKind
import org.opentaint.ir.api.python.PIRPosExpr
import org.opentaint.ir.api.python.PIRPowExpr
import org.opentaint.ir.api.python.PIRRShiftExpr
import org.opentaint.ir.api.python.PIRSubExpr
import org.opentaint.ir.api.python.PIRUnaryExpr
import org.opentaint.ir.api.python.PIRValue
import org.opentaint.ir.impl.python.PIRDecoratorImpl
import org.opentaint.ir.impl.python.flat.FlatArgKind
import org.opentaint.ir.impl.python.flat.FlatBinaryOperator
import org.opentaint.ir.impl.python.flat.FlatCompareOperator
import org.opentaint.ir.impl.python.flat.FlatDecorator
import org.opentaint.ir.impl.python.flat.FlatParamKind
import org.opentaint.ir.impl.python.flat.FlatUnaryOperator

internal fun FlatParamKind.toPir(): PIRParameterKind = when (this) {
    FlatParamKind.POSITIONAL_OR_KEYWORD -> PIRParameterKind.POSITIONAL_OR_KEYWORD
    FlatParamKind.VAR_POSITIONAL -> PIRParameterKind.VAR_POSITIONAL
    FlatParamKind.VAR_KEYWORD -> PIRParameterKind.VAR_KEYWORD
    FlatParamKind.KEYWORD_ONLY -> PIRParameterKind.KEYWORD_ONLY
}

internal fun FlatArgKind.toPir(): PIRCallArgKind = when (this) {
    FlatArgKind.POSITIONAL -> PIRCallArgKind.POSITIONAL
    FlatArgKind.KEYWORD -> PIRCallArgKind.KEYWORD
    FlatArgKind.STAR -> PIRCallArgKind.STAR
    FlatArgKind.DOUBLE_STAR -> PIRCallArgKind.DOUBLE_STAR
}

internal fun FlatBinaryOperator.toPir(l: PIRValue, r: PIRValue): PIRBinaryExpr = when (this) {
    FlatBinaryOperator.ADD -> PIRAddExpr(l, r)
    FlatBinaryOperator.SUB -> PIRSubExpr(l, r)
    FlatBinaryOperator.MUL -> PIRMulExpr(l, r)
    FlatBinaryOperator.DIV -> PIRDivExpr(l, r)
    FlatBinaryOperator.FLOOR_DIV -> PIRFloorDivExpr(l, r)
    FlatBinaryOperator.MOD -> PIRModExpr(l, r)
    FlatBinaryOperator.POW -> PIRPowExpr(l, r)
    FlatBinaryOperator.MAT_MUL -> PIRMatMulExpr(l, r)
    FlatBinaryOperator.BIT_AND -> PIRBitAndExpr(l, r)
    FlatBinaryOperator.BIT_OR -> PIRBitOrExpr(l, r)
    FlatBinaryOperator.BIT_XOR -> PIRBitXorExpr(l, r)
    FlatBinaryOperator.LSHIFT -> PIRLShiftExpr(l, r)
    FlatBinaryOperator.RSHIFT -> PIRRShiftExpr(l, r)
}

internal fun FlatUnaryOperator.toPir(operand: PIRValue): PIRUnaryExpr = when (this) {
    FlatUnaryOperator.NEG -> PIRNegExpr(operand)
    FlatUnaryOperator.POS -> PIRPosExpr(operand)
    FlatUnaryOperator.NOT -> PIRNotExpr(operand)
    FlatUnaryOperator.INVERT -> PIRInvertExpr(operand)
}

internal fun FlatCompareOperator.toPir(l: PIRValue, r: PIRValue): PIRCompareExpr = when (this) {
    FlatCompareOperator.EQ -> PIREqExpr(l, r)
    FlatCompareOperator.NE -> PIRNeExpr(l, r)
    FlatCompareOperator.LT -> PIRLtExpr(l, r)
    FlatCompareOperator.LE -> PIRLeExpr(l, r)
    FlatCompareOperator.GT -> PIRGtExpr(l, r)
    FlatCompareOperator.GE -> PIRGeExpr(l, r)
    FlatCompareOperator.IS -> PIRIsExpr(l, r)
    FlatCompareOperator.IS_NOT -> PIRIsNotExpr(l, r)
    FlatCompareOperator.IN -> PIRInExpr(l, r)
    FlatCompareOperator.NOT_IN -> PIRNotInExpr(l, r)
}

internal fun FlatDecorator.toPir(): PIRDecoratorImpl =
    PIRDecoratorImpl(name, qualifiedName, arguments)

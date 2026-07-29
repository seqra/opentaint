package org.opentaint.dataflow.jvm.util

import org.objectweb.asm.Opcodes
import org.opentaint.ir.api.jvm.JIRMethod
import org.opentaint.ir.api.jvm.cfg.JIRMethodCallExpr

fun JIRMethod.isVararg(): Boolean =
    access and Opcodes.ACC_VARARGS != 0

fun JIRMethodCallExpr.isVararg(): Boolean =
    method.method.isVararg()

fun JIRMethod.varargParamIdx(): Int =
    parameters.lastIndex

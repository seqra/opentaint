package org.opentaint.ir.impl.python.flatToPir

import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRModule
import org.opentaint.ir.api.python.PIRProperty
import org.opentaint.ir.impl.python.PIRClassImpl
import org.opentaint.ir.impl.python.PIRFieldImpl
import org.opentaint.ir.impl.python.PIRFunctionImpl
import org.opentaint.ir.impl.python.PIRModuleImpl
import org.opentaint.ir.impl.python.PIRParameterImpl
import org.opentaint.ir.impl.python.PIRPropertyImpl
import org.opentaint.ir.impl.python.flat.FlatClass
import org.opentaint.ir.impl.python.flat.FlatFunctionIR
import org.opentaint.ir.impl.python.flat.FlatModuleIR

class FlatToPirConverter(
    private val flat: FlatModuleIR,
) {
    fun convert(): PIRModule {
        val pirFunctions = flat.functions.map { convertFlatFunction(it) }
        val pirModuleInit = convertFlatFunction(flat.moduleInit)
        val pirClasses = flat.classes.map { flatClassToPir(it) }
        val pirFields = flat.fields.map {
            PIRFieldImpl(it.name, TypeConverter.convert(it.type), isClassVar = false)
        }

        return PIRModuleImpl(
            name = flat.moduleName,
            path = flat.path,
            classes = pirClasses,
            functions = pirFunctions,
            fields = pirFields,
            moduleInit = pirModuleInit,
            diagnostics = flat.diagnostics,
        ).also { wireModuleBackRefs(it) }
    }

    private fun wireModuleBackRefs(module: PIRModuleImpl) {
        for (fn in module.functions) wireFunctionModule(fn, module)
        wireFunctionModule(module.moduleInit, module)
        for (cls in module.classes) wireClassModule(cls as PIRClassImpl, module)
    }

    private fun wireFunctionModule(fn: PIRFunction, module: PIRModule) {
        (fn as PIRFunctionImpl).module = module
    }

    private fun wireClassModule(cls: PIRClassImpl, module: PIRModule) {
        cls.module = module
        for (method in cls.methods) wireFunctionModule(method, module)
        for (nested in cls.nestedClasses) wireClassModule(nested as PIRClassImpl, module)
    }

    private fun flatClassToPir(flat: FlatClass): PIRClass {
        val methods = flat.methods.map { convertFlatFunction(it) }
        val classFields = flat.fields.map {
            PIRFieldImpl(it.name, TypeConverter.convert(it.type), it.isClassVar)
        }
        val nestedClasses = flat.nestedClasses.map { flatClassToPir(it) }
        val properties = synthesizeProperties(flat.methods, methods)
        val decorators = flat.decorators.map { it.toPir() }

        val cls = PIRClassImpl(
            name = flat.name,
            qualifiedName = flat.qualifiedName,
            baseClasses = flat.baseClasses,
            mro = flat.mro,
            methods = methods,
            fields = classFields,
            nestedClasses = nestedClasses,
            properties = properties,
            decorators = decorators,
            isAbstract = flat.isAbstract,
            isDataclass = flat.isDataclass,
            isEnum = flat.isEnum,
        )

        for (method in methods) {
            method.enclosingClass = cls
        }

        return cls
    }

    private fun synthesizeProperties(
        flatMethods: List<FlatFunctionIR>,
        pirMethods: List<PIRFunctionImpl>,
    ): List<PIRProperty> {
        val methods = flatMethods.zip(pirMethods)
        val byName = methods.groupBy { (flat, _) -> flat.name }
        return methods
            .filter { (flat, _) -> flat.isProperty }
            .distinctBy { (flat, _) -> flat.name }
            .map { (getterFlat, getterPir) ->
                val group = byName.getValue(getterFlat.name)
                PIRPropertyImpl(
                    name = getterFlat.name,
                    type = getterPir.returnType,
                    getter = getterPir,
                    setter = group.accessorFor("setter"),
                    deleter = group.accessorFor("deleter"),
                )
            }
    }

    private fun List<Pair<FlatFunctionIR, PIRFunctionImpl>>.accessorFor(
        decorator: String,
    ): PIRFunctionImpl? =
        firstOrNull { (flat, _) -> flat.decorators.any { it.name == decorator } }?.second

    private fun convertFlatFunction(pending: FlatFunctionIR): PIRFunctionImpl {
        val params = pending.parameters.mapIndexed { idx, p ->
            PIRParameterImpl(
                p.name,
                TypeConverter.convert(p.type),
                p.kind.toPir(),
                p.hasDefault,
                p.defaultValue?.let { ConstConverter.convert(it) },
                idx,
            )
        }
        val returnType = TypeConverter.convert(pending.returnType)
        val cfgResult = CfgConverter.convert(pending.cfg, pending.parameters, pending.qualifiedName)

        val function = PIRFunctionImpl(
            name = pending.name,
            qualifiedName = pending.qualifiedName,
            parameters = params,
            returnType = returnType,
            cfg = cfgResult.cfg,
            decorators = pending.decorators.map { it.toPir() },
            isAsync = pending.isAsync,
            isGenerator = pending.isGenerator,
            isStaticMethod = pending.isStaticMethod,
            isClassMethod = pending.isClassMethod,
            isProperty = pending.isProperty,
            closureVars = pending.closureVars.toList(),
            enclosingClass = null,
        )
        for (loc in cfgResult.locations) loc.method = function
        return function
    }
}

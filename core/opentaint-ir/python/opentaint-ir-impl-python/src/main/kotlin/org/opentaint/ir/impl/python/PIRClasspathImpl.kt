package org.opentaint.ir.impl.python

import org.opentaint.ir.api.python.PIRClass
import org.opentaint.ir.api.python.PIRClasspath
import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRModule

class PIRClasspathImpl internal constructor(
    override val pythonVersion: String,
    override val mypyVersion: String,
    override val modules: List<PIRModule>,
    private val modulesByName: Map<String, PIRModule>,
    private val classesByQName: Map<String, PIRClass>,
    private val functionsByQName: Map<String, PIRFunction>,
) : PIRClasspath {

    override fun findModuleOrNull(name: String): PIRModule? = modulesByName[name]
    override fun findClassOrNull(qualifiedName: String): PIRClass? = classesByQName[qualifiedName]
    override fun findFunctionOrNull(qualifiedName: String): PIRFunction? = functionsByQName[qualifiedName]
}

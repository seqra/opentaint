package org.opentaint.ir.impl.python

import org.opentaint.ir.api.python.PIRFunction
import org.opentaint.ir.api.python.PIRLocation

class PIRLocationImpl(
    override val index: Int,
) : PIRLocation {
    override lateinit var method: PIRFunction

    override fun toString(): String = "PIRLocation(index=$index)"
}

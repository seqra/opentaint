package org.opentaint.dataflow.jvm.ap.ifds.taint

import org.opentaint.dataflow.configuration.jvm.JirCondition
import org.opentaint.dataflow.configuration.jvm.JirConditionVisitor
import org.opentaint.dataflow.configuration.jvm.Position
import org.opentaint.dataflow.configuration.jvm.TaintMark
import java.util.Objects

@Suppress("EqualsOrHashCode")
data class ContainsMarkOnAnyField(
    val position: Position,
    val mark: TaintMark,
) : JirCondition {
    override fun <R> accept(conditionVisitor: JirConditionVisitor<R>): R {
        error("Condition visitor is not supported")
    }

    private val hash = Objects.hash(position, mark)
    override fun hashCode(): Int = hash
}

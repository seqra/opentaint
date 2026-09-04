package org.opentaint.jvm.sast.dataflow.rules

import org.opentaint.dataflow.configuration.CommonCondition
import org.opentaint.dataflow.configuration.jvm.Condition
import java.util.concurrent.ConcurrentHashMap

class ResolvedRuleInterner {
    private val values = ConcurrentHashMap<Any, Any>()

    @Suppress("UNCHECKED_CAST")
    fun <T : Any> intern(value: T): T {
        values[value]?.let { return it as T }
        return (values.putIfAbsent(value, value) ?: value) as T
    }

    fun <T : Any> internList(list: List<T>): List<T> {
        if (list.isEmpty()) return emptyList()
        return intern(list.mapTo(ArrayList(list.size)) { intern(it) })
    }

    fun internCondition(condition: Condition): Condition = when (condition) {
        is CommonCondition.True -> condition

        is CommonCondition.Atom -> intern(CommonCondition.Atom(intern(condition.atom)))

        is CommonCondition.Not -> intern(CommonCondition.Not(internCondition(condition.arg)))

        is CommonCondition.And -> intern(
            CommonCondition.And(internList(condition.args.map { internCondition(it) }))
        )

        is CommonCondition.Or -> intern(
            CommonCondition.Or(internList(condition.args.map { internCondition(it) }))
        )
    }
}

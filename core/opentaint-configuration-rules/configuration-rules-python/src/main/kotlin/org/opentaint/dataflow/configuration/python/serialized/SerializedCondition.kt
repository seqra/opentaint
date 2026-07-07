package org.opentaint.dataflow.configuration.python.serialized

import com.charleskorn.kaml.YamlContentPolymorphicSerializer
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.Serializable

/**
 * Sink condition predicate. Supports boolean composition (`anyOf` / `allOf` / `not`)
 * and the primitive `ContainsMark` check (`tainted: <kind>` at `pos:`).
 *
 * The shipped Python config only uses `anyOf` + `ContainsMark`; the other operators are
 * kept for parity with the JVM config and future extension.
 */
@Serializable(with = SerializedPythonConditionSerializer::class)
sealed interface SerializedPythonCondition {
    @Serializable
    data class Or(val anyOf: List<SerializedPythonCondition>) : SerializedPythonCondition

    @Serializable
    data class And(val allOf: List<SerializedPythonCondition>) : SerializedPythonCondition

    @Serializable
    data class Not(val not: SerializedPythonCondition) : SerializedPythonCondition

    /** `tainted: <kind>` paired with `pos: <position>`. */
    @Serializable
    data class ContainsMark(
        val tainted: String,
        val pos: PythonPosition,
    ) : SerializedPythonCondition

    @Serializable
    data class ContainsMarkOnAnyAccessor(
        val tainted: String,
        val pos: PythonPosition,
    ) : SerializedPythonCondition

    /** Call-arity predicate: the matched call passes exactly `n` positional arguments. */
    @Serializable
    data class NumberOfArgs(val n: Int) : SerializedPythonCondition

    /** The argument at [pos] is a constant literal comparing [cmp] to [value]. */
    @Serializable
    data class ConstantCmp(
        val pos: PythonPosition,
        val value: ConstantValue,
        val cmp: ConstantCmpType,
    ) : SerializedPythonCondition

    /** The argument at [pos] is a string constant matching the regex [pattern]. */
    @Serializable
    data class ConstantMatches(
        val pos: PythonPosition,
        val pattern: String,
    ) : SerializedPythonCondition

    @Serializable
    data class ConstantValue(val type: ConstantType, val value: String)

    enum class ConstantCmpType { Eq, Lt, Gt }

    enum class ConstantType { Bool, Int, Str }
}

class SerializedPythonConditionSerializer :
    YamlContentPolymorphicSerializer<SerializedPythonCondition>(SerializedPythonCondition::class) {
    override fun selectDeserializer(node: YamlNode): DeserializationStrategy<SerializedPythonCondition> {
        if (node !is YamlMap) error("Unexpected condition node: $node")
        for ((property, serializer) in serializerByProperty) {
            if (node.getKey(property) != null) return serializer
        }
        error("Unexpected condition node: $node")
    }

    companion object {
        private val serializerByProperty = mapOf(
            "anyOf" to SerializedPythonCondition.Or.serializer(),
            "allOf" to SerializedPythonCondition.And.serializer(),
            "not" to SerializedPythonCondition.Not.serializer(),
            "tainted" to SerializedPythonCondition.ContainsMark.serializer(),
            "taintedAny" to SerializedPythonCondition.ContainsMarkOnAnyAccessor.serializer(),
            "n" to SerializedPythonCondition.NumberOfArgs.serializer(),
            "cmp" to SerializedPythonCondition.ConstantCmp.serializer(),
            "pattern" to SerializedPythonCondition.ConstantMatches.serializer(),
        )
    }
}

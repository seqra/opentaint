package org.opentaint.dataflow.configuration.python.serialized

import com.charleskorn.kaml.YamlContentPolymorphicSerializer
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable(with = SerializedPythonConditionSerializer::class)
sealed interface SerializedPythonCondition {
    @Serializable
    data class Or(val anyOf: List<SerializedPythonCondition>) : SerializedPythonCondition

    @Serializable
    data class And(val allOf: List<SerializedPythonCondition>) : SerializedPythonCondition

    @Serializable
    data class Not(val not: SerializedPythonCondition) : SerializedPythonCondition

    @Serializable
    data class ContainsMark(
        val tainted: String,
        val pos: PythonPosition,
    ) : SerializedPythonCondition

    @Serializable
    data class ContainsMarkOnAnyAccessor(
        @SerialName("taintedAny") val tainted: String,
        val pos: PythonPosition,
    ) : SerializedPythonCondition

    @Serializable
    data class NumberOfArgs(val n: Int) : SerializedPythonCondition

    @Serializable
    data class MethodDecorated(val decorator: String) : SerializedPythonCondition

    @Serializable
    data class ClassExtends(val baseClass: String) : SerializedPythonCondition

    @Serializable
    data class ConstantCmp(
        val pos: PythonPosition,
        val value: ConstantValue,
        val cmp: ConstantCmpType,
    ) : SerializedPythonCondition

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
            "decorator" to SerializedPythonCondition.MethodDecorated.serializer(),
            "baseClass" to SerializedPythonCondition.ClassExtends.serializer(),
        )
    }
}

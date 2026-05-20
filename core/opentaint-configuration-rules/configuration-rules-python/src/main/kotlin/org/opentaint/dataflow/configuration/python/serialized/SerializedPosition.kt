package org.opentaint.dataflow.configuration.python.serialized

import com.charleskorn.kaml.YamlContentPolymorphicSerializer
import com.charleskorn.kaml.YamlList
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.YamlScalar
import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.InternalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.SerialKind
import kotlinx.serialization.descriptors.buildSerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

/**
 * Base position of a value the rule talks about: a positional arg, a keyword arg,
 * the implicit `self` receiver, the call result, or a class-scoped attribute
 * (e.g. `class(flask.request)` denotes accessing `flask.request` inside the rule's scope).
 */
@Serializable(with = PythonPositionBaseSerializer::class)
sealed interface PythonPositionBase {
    /** `arg(N)` or `arg(*)` (the wildcard form is only valid in entry-point rules). */
    data class Argument(val idx: Int?) : PythonPositionBase

    /** `kwarg(name)` — a keyword argument by name. */
    data class KwArgument(val name: String) : PythonPositionBase

    /** `this` — the implicit receiver of a method call. */
    data object This : PythonPositionBase

    /** `result` — the return value of a call (or the value of an `attribute:` access). */
    data object Result : PythonPositionBase

    /**
     * `class(fqn)` — references a value accessible via fully-qualified class/attribute path.
     * In the Python config this appears only as `class(flask.request)` to taint accesses
     * to `flask.request` inside entry-point methods.
     */
    data class ClassRef(val fqn: String) : PythonPositionBase

    fun serializedStr(): String = when (this) {
        is Argument -> "arg(${idx ?: "*"})"
        is KwArgument -> "kwarg($name)"
        is ClassRef -> "class($fqn)"
        Result -> "result"
        This -> "this"
    }

    companion object {
        private val argPattern = Regex("""arg\((\d+|\*)\)""")
        private val kwargPattern = Regex("""kwarg\(([^)]+)\)""")
        private val classPattern = Regex("""class\(([^)]+)\)""")

        fun deserialize(str: String): PythonPositionBase {
            return when (str) {
                "this" -> This
                "result" -> Result
                else -> {
                    argPattern.matchEntire(str)?.let { m ->
                        val raw = m.groupValues[1]
                        return Argument(if (raw == "*") null else raw.toInt())
                    }
                    kwargPattern.matchEntire(str)?.let { m ->
                        return KwArgument(m.groupValues[1])
                    }
                    classPattern.matchEntire(str)?.let { m ->
                        return ClassRef(m.groupValues[1])
                    }
                    error("Unexpected position: $str")
                }
            }
        }
    }
}

object PythonPositionBaseSerializer : KSerializer<PythonPositionBase> {
    override val descriptor: SerialDescriptor
        get() = PrimitiveSerialDescriptor("python.position", PrimitiveKind.STRING)

    override fun deserialize(decoder: Decoder): PythonPositionBase =
        PythonPositionBase.deserialize(decoder.decodeString())

    override fun serialize(encoder: Encoder, value: PythonPositionBase) {
        encoder.encodeString(value.serializedStr())
    }
}

/**
 * A position, optionally extended with access-path modifiers (currently only `[*]` —
 * "any element of the collection"). YAML may encode this either as a scalar (no
 * modifiers) or as a list whose first element is the base.
 *
 * Example list form:
 *   pos:
 *   - kwarg(messages)
 *   - '[*]'
 */
@Serializable(with = PythonPositionSerializer::class)
sealed interface PythonPosition {
    val base: PythonPositionBase

    @Serializable(with = BaseOnlyPythonPositionSerializer::class)
    data class BaseOnly(override val base: PythonPositionBase) : PythonPosition

    @Serializable(with = WithModifiersPythonPositionSerializer::class)
    data class WithModifiers(
        override val base: PythonPositionBase,
        val modifiers: List<PythonPositionModifier>
    ) : PythonPosition
}

sealed interface PythonPositionModifier {
    /** `[*]` — any array element at this position. */
    data object ArrayElement : PythonPositionModifier

    /** `.<name>` — access the named attribute/field of the value at this position. */
    data class Field(val name: String) : PythonPositionModifier

    fun serializedStr(): String = when (this) {
        ArrayElement -> "[*]"
        is Field -> ".$name"
    }

    companion object {
        fun deserialize(str: String): PythonPositionModifier = when {
            str == "[*]" -> ArrayElement
            str.startsWith(".") -> Field(str.substring(1))
            else -> error("Unexpected position modifier: $str")
        }
    }
}

class PythonPositionSerializer :
    YamlContentPolymorphicSerializer<PythonPosition>(PythonPosition::class) {

    @OptIn(InternalSerializationApi::class, ExperimentalSerializationApi::class)
    override val descriptor: SerialDescriptor
        get() = buildSerialDescriptor(serialName = super.descriptor.serialName, kind = SerialKind.CONTEXTUAL) {
            annotations = super.descriptor.annotations
        }

    override fun selectDeserializer(node: YamlNode): DeserializationStrategy<PythonPosition> = when (node) {
        is YamlScalar -> PythonPosition.BaseOnly.serializer()
        is YamlList -> PythonPosition.WithModifiers.serializer()
        else -> error("Unexpected node: $node")
    }
}

class BaseOnlyPythonPositionSerializer : KSerializer<PythonPosition.BaseOnly> {
    override val descriptor: SerialDescriptor
        get() = PythonPositionBaseSerializer.descriptor

    override fun deserialize(decoder: Decoder): PythonPosition.BaseOnly =
        PythonPosition.BaseOnly(PythonPositionBaseSerializer.deserialize(decoder))

    override fun serialize(encoder: Encoder, value: PythonPosition.BaseOnly) {
        PythonPositionBaseSerializer.serialize(encoder, value.base)
    }
}

class WithModifiersPythonPositionSerializer : KSerializer<PythonPosition.WithModifiers> {
    private val stringListSerializer = ListSerializer(String.serializer())

    override val descriptor: SerialDescriptor
        get() = stringListSerializer.descriptor

    override fun deserialize(decoder: Decoder): PythonPosition.WithModifiers {
        val strings = stringListSerializer.deserialize(decoder)
        check(strings.isNotEmpty()) { "Position list must not be empty" }
        val base = PythonPositionBase.deserialize(strings.first())
        val modifiers = strings.drop(1).map { PythonPositionModifier.deserialize(it) }
        return PythonPosition.WithModifiers(base, modifiers)
    }

    override fun serialize(encoder: Encoder, value: PythonPosition.WithModifiers) {
        val strings = listOf(value.base.serializedStr()) + value.modifiers.map { it.serializedStr() }
        stringListSerializer.serialize(encoder, strings)
    }
}

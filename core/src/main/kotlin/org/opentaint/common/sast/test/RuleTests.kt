package org.opentaint.common.sast.test

import com.charleskorn.kaml.YamlContentPolymorphicSerializer
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.YamlScalar
import kotlinx.serialization.DeserializationStrategy
import kotlinx.serialization.KSerializer
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

const val DEFAULT_SAMPLE_MODE = "default"
const val SPRING_APP_SAMPLE_MODE = "spring-app"

@Serializable
data class RuleTests(
    val tests: List<RuleTest>,
)

@Serializable
data class RuleTest(
    @SerialName("rule-id")
    val ruleId: String,
    val positive: List<RuleSample> = emptyList(),
    val negative: List<RuleSample> = emptyList(),
)

@Serializable(with = RuleSampleSerializer::class)
data class RuleSample(
    val entrypoint: String,
    val mode: String = DEFAULT_SAMPLE_MODE,
)

@Serializable
private data class RuleSampleObject(
    val entrypoint: String,
    val mode: String = DEFAULT_SAMPLE_MODE,
)

class RuleSampleSerializer : YamlContentPolymorphicSerializer<RuleSample>(RuleSample::class) {
    override fun selectDeserializer(node: YamlNode): DeserializationStrategy<RuleSample> = when (node) {
        is YamlScalar -> RuleSampleScalarSerializer
        else -> RuleSampleObjectSerializer
    }
}

object RuleSampleScalarSerializer : KSerializer<RuleSample> {
    override val descriptor: SerialDescriptor = PrimitiveSerialDescriptor("RuleSample", PrimitiveKind.STRING)
    override fun deserialize(decoder: Decoder): RuleSample = RuleSample(decoder.decodeString())
    override fun serialize(encoder: Encoder, value: RuleSample) = encoder.encodeString(value.entrypoint)
}

object RuleSampleObjectSerializer : KSerializer<RuleSample> {
    private val delegate = RuleSampleObject.serializer()
    override val descriptor: SerialDescriptor = delegate.descriptor
    override fun deserialize(decoder: Decoder): RuleSample =
        decoder.decodeSerializableValue(delegate).let { RuleSample(it.entrypoint, it.mode) }
    override fun serialize(encoder: Encoder, value: RuleSample) =
        encoder.encodeSerializableValue(delegate, RuleSampleObject(value.entrypoint, value.mode))
}

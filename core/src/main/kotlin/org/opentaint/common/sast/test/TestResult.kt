package org.opentaint.common.sast.test

import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.SerializationException
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlin.reflect.KClass

@Serializable
data class RuleInfo(val rulePath: String, val ruleId: String?)

interface TestSampleInfo {
    val language: String
    val testSetName: String
}

@Serializable
data class TestResult<T : TestSampleInfo>(
    val success: List<T>,
    val falseNegative: List<T>,
    val falsePositive: List<T>,
    val skipped: List<T>,
    val disabled: List<T>,
)

fun <T : TestSampleInfo> List<TestResult<T>>.joinResults(): TestResult<T> = TestResult(
    success = flatMap { it.success },
    falseNegative = flatMap { it.falseNegative },
    falsePositive = flatMap { it.falsePositive },
    skipped = flatMap { it.skipped },
    disabled = flatMap { it.disabled },
)

class TestSampleInfoSerializer(
    serializers: List<Pair<KClass<TestSampleInfo>, KSerializer<TestSampleInfo>>>
) : KSerializer<TestSampleInfo> {
    private val serializers = serializers.associateBy({ it.first }, { it.second })

    override val descriptor: SerialDescriptor = buildClassSerialDescriptor("TestSampleInfo")

    override fun serialize(encoder: Encoder, value: TestSampleInfo) {
        val serializer = serializers[value::class] ?: throw SerializationException(
            "Serializer is not registered for test sample info: ${value::class.qualifiedName}"
        )
        encoder.encodeSerializableValue(serializer, value)
    }

    override fun deserialize(decoder: Decoder): TestSampleInfo {
        throw SerializationException("TestSampleInfo deserialization is not supported")
    }
}

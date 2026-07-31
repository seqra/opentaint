package org.opentaint.dataflow.configuration.python.serialized

import kotlinx.serialization.KSerializer
import kotlinx.serialization.Serializable
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

/**
 * Sink metadata. `cwe` may be omitted (e.g. for `prompt-injection` / `template-injection`).
 * `note` is the canonical short name of the vulnerability category and is also used by
 * cleaner rules' `for:` field to scope cleaning to a specific sink category.
 */
@Serializable
data class PythonSinkMetaData(
    val cwe: List<Int>? = null,
    val note: String? = null,
)

sealed interface SerializedPythonRule {
    /** Identifies what the rule fires on — a function call or an attribute access. */
    val target: PythonTarget

    val info: ItemInfo?

    /** Assigned by the semgrep converter; identifies the rule within its generated group. */
    val serializedId: String?
}

/** Rules that emit taint (entry-point parameters or arbitrary calls/attributes). */
sealed interface SerializedPythonSourceRule : SerializedPythonRule {
    val condition: SerializedPythonCondition?
    val taint: List<SerializedPythonTaintAssignAction>
}

/**
 * Entry-point source — fires when control reaches a function matched by the rule,
 * tainting the listed positions before the function executes. Distinct from a regular
 * [SerializedPythonSource] because the rule's `function:` matcher is typically a regex
 * or unqualified name (e.g. `.*`, `dispatch_request`), narrowed by a structural
 * condition such as [SerializedPythonCondition.MethodDecorated].
 */
@Serializable(with = SerializedPythonEntryPointSerializer::class)
data class SerializedPythonEntryPointSource(
    override val target: PythonTarget,
    override val condition: SerializedPythonCondition? = null,
    override val taint: List<SerializedPythonTaintAssignAction>,
    override val info: ItemInfo? = null,
    override val serializedId: String? = null,
) : SerializedPythonSourceRule

/** Regular source — taints the result of a call or attribute access. */
@Serializable(with = SerializedPythonSourceSerializer::class)
data class SerializedPythonSource(
    override val target: PythonTarget,
    override val condition: SerializedPythonCondition? = null,
    override val taint: List<SerializedPythonTaintAssignAction>,
    override val info: ItemInfo? = null,
    override val serializedId: String? = null,
) : SerializedPythonSourceRule

@Serializable(with = SerializedPythonSinkSerializer::class)
data class SerializedPythonSink(
    override val target: PythonTarget,
    val condition: SerializedPythonCondition? = null,
    val meta: PythonSinkMetaData? = null,
    override val info: ItemInfo? = null,
    override val serializedId: String? = null,
) : SerializedPythonRule

/** Return (method-exit) sink — fires at the analyzed method's own `return`; mirrors JVM `MethodExitSink`. */
@Serializable(with = SerializedPythonExitSinkSerializer::class)
data class SerializedPythonExitSink(
    override val target: PythonTarget,
    val condition: SerializedPythonCondition? = null,
    val meta: PythonSinkMetaData? = null,
    override val info: ItemInfo? = null,
    override val serializedId: String? = null,
) : SerializedPythonRule

@Serializable(with = SerializedPythonPassThroughSerializer::class)
data class SerializedPythonPassThrough(
    override val target: PythonTarget,
    val condition: SerializedPythonCondition? = null,
    val copy: List<SerializedPythonTaintPassAction>,
    override val info: ItemInfo? = null,
    override val serializedId: String? = null,
) : SerializedPythonRule

/**
 * `for: <note>` scopes the cleaner to sinks with a matching `note:` value
 * (e.g. cleaning only applies for `url-redirection` sinks).
 */
@Serializable(with = SerializedPythonCleanerSerializer::class)
data class SerializedPythonCleaner(
    override val target: PythonTarget,
    val condition: SerializedPythonCondition? = null,
    val cleans: List<SerializedPythonTaintCleanAction>,
    val `for`: String? = null,
    override val info: ItemInfo? = null,
    override val serializedId: String? = null,
) : SerializedPythonRule

// region Surrogates
// Rules carry `function:` / `attribute:` / `signature:` as flat top-level keys in YAML
// for readability, but the in-memory model nests them inside `target: PythonTarget`.
// Each rule deserializes via a flat surrogate which is then folded into the target.

private fun buildTarget(function: String?, attribute: String?, signature: SerializedPythonSignatureMatcher?): PythonTarget {
    return when {
        function != null && attribute != null ->
            error("Rule cannot specify both 'function:' and 'attribute:'")
        function != null -> PythonTarget.Function(function, signature)
        attribute != null -> {
            require(signature == null) { "'signature:' is only valid with 'function:'" }
            PythonTarget.Attribute(attribute)
        }
        else -> error("Rule must specify 'function:' or 'attribute:'")
    }
}

@Serializable
private data class EntryPointSurrogate(
    val function: String? = null,
    val attribute: String? = null,
    val signature: SerializedPythonSignatureMatcher? = null,
    val condition: SerializedPythonCondition? = null,
    val taint: List<SerializedPythonTaintAssignAction>,
)

object SerializedPythonEntryPointSerializer : KSerializer<SerializedPythonEntryPointSource> {
    override val descriptor: SerialDescriptor = EntryPointSurrogate.serializer().descriptor
    override fun deserialize(decoder: Decoder): SerializedPythonEntryPointSource {
        val raw = decoder.decodeSerializableValue(EntryPointSurrogate.serializer())
        return SerializedPythonEntryPointSource(
            target = buildTarget(raw.function, raw.attribute, raw.signature),
            condition = raw.condition,
            taint = raw.taint,
        )
    }
    override fun serialize(encoder: Encoder, value: SerializedPythonEntryPointSource) = unsupported()
}

@Serializable
private data class SourceSurrogate(
    val function: String? = null,
    val attribute: String? = null,
    val signature: SerializedPythonSignatureMatcher? = null,
    val condition: SerializedPythonCondition? = null,
    val taint: List<SerializedPythonTaintAssignAction>,
)

object SerializedPythonSourceSerializer : KSerializer<SerializedPythonSource> {
    override val descriptor: SerialDescriptor = SourceSurrogate.serializer().descriptor
    override fun deserialize(decoder: Decoder): SerializedPythonSource {
        val raw = decoder.decodeSerializableValue(SourceSurrogate.serializer())
        return SerializedPythonSource(
            target = buildTarget(raw.function, raw.attribute, raw.signature),
            condition = raw.condition,
            taint = raw.taint,
        )
    }
    override fun serialize(encoder: Encoder, value: SerializedPythonSource) = unsupported()
}

@Serializable
private data class SinkSurrogate(
    val function: String? = null,
    val attribute: String? = null,
    val signature: SerializedPythonSignatureMatcher? = null,
    val condition: SerializedPythonCondition? = null,
    val cwe: List<Int>? = null,
    val note: String? = null,
)

object SerializedPythonSinkSerializer : KSerializer<SerializedPythonSink> {
    override val descriptor: SerialDescriptor = SinkSurrogate.serializer().descriptor
    override fun deserialize(decoder: Decoder): SerializedPythonSink {
        val raw = decoder.decodeSerializableValue(SinkSurrogate.serializer())
        return SerializedPythonSink(
            target = buildTarget(raw.function, raw.attribute, raw.signature),
            condition = raw.condition,
            meta = PythonSinkMetaData(raw.cwe, raw.note),
        )
    }
    override fun serialize(encoder: Encoder, value: SerializedPythonSink) = unsupported()
}

object SerializedPythonExitSinkSerializer : KSerializer<SerializedPythonExitSink> {
    override val descriptor: SerialDescriptor = SinkSurrogate.serializer().descriptor
    override fun deserialize(decoder: Decoder): SerializedPythonExitSink {
        val raw = decoder.decodeSerializableValue(SinkSurrogate.serializer())
        return SerializedPythonExitSink(
            target = buildTarget(raw.function, raw.attribute, raw.signature),
            condition = raw.condition,
            meta = PythonSinkMetaData(raw.cwe, raw.note),
        )
    }
    override fun serialize(encoder: Encoder, value: SerializedPythonExitSink) = unsupported()
}

@Serializable
private data class PassThroughSurrogate(
    val function: String? = null,
    val attribute: String? = null,
    val signature: SerializedPythonSignatureMatcher? = null,
    val condition: SerializedPythonCondition? = null,
    val copy: List<SerializedPythonTaintPassAction>,
)

object SerializedPythonPassThroughSerializer : KSerializer<SerializedPythonPassThrough> {
    override val descriptor: SerialDescriptor = PassThroughSurrogate.serializer().descriptor
    override fun deserialize(decoder: Decoder): SerializedPythonPassThrough {
        val raw = decoder.decodeSerializableValue(PassThroughSurrogate.serializer())
        return SerializedPythonPassThrough(
            target = buildTarget(raw.function, raw.attribute, raw.signature),
            condition = raw.condition,
            copy = raw.copy,
        )
    }
    override fun serialize(encoder: Encoder, value: SerializedPythonPassThrough) = unsupported()
}

@Serializable
private data class CleanerSurrogate(
    val function: String? = null,
    val attribute: String? = null,
    val signature: SerializedPythonSignatureMatcher? = null,
    val condition: SerializedPythonCondition? = null,
    val cleans: List<SerializedPythonTaintCleanAction>,
    val `for`: String? = null,
)

object SerializedPythonCleanerSerializer : KSerializer<SerializedPythonCleaner> {
    override val descriptor: SerialDescriptor = CleanerSurrogate.serializer().descriptor
    override fun deserialize(decoder: Decoder): SerializedPythonCleaner {
        val raw = decoder.decodeSerializableValue(CleanerSurrogate.serializer())
        return SerializedPythonCleaner(
            target = buildTarget(raw.function, raw.attribute, raw.signature),
            condition = raw.condition,
            cleans = raw.cleans,
            `for` = raw.`for`,
        )
    }
    override fun serialize(encoder: Encoder, value: SerializedPythonCleaner) = unsupported()
}

private fun unsupported(): Nothing = error("Serialization of Python rules is not supported")
// endregion

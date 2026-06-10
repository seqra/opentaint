package org.opentaint.go.config

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.YamlList
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.YamlScalar
import org.opentaint.dataflow.configuration.go.serialized.GoNameMatcher
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedPassAction
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedRule
import org.opentaint.dataflow.configuration.go.serialized.GoSerializedTaintConfig
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier
import java.io.InputStream
import java.nio.file.FileSystems
import java.nio.file.Files
import java.util.Collections
import kotlin.streams.asSequence

object GoConfigLoader {
    private const val CONFIG_ROOT = "/go-config"
    private val config = lazy { loadConfig() }

    fun getConfig(): GoSerializedTaintConfig? = config.value

    private fun loadConfig(): GoSerializedTaintConfig? {
        val resources = javaClass.getResource(CONFIG_ROOT) ?: return null
        val uri = resources.toURI()
        if (uri.scheme != "jar") return null

        val files = FileSystems.newFileSystem(uri, Collections.emptyMap<String, String>()).use { fs ->
            val path = fs.getPath(CONFIG_ROOT)
            Files.walk(path).asSequence()
                .map { path.relativize(it).toString() }
                .filter { it.endsWith(".yaml") }
                .toList()
        }
        if (files.isEmpty()) return null

        val passThrough = mutableListOf<GoSerializedRule.PassThrough>()
        for (file in files) {
            javaClass.getResourceAsStream("$CONFIG_ROOT/$file").use { stream ->
                if (stream != null) passThrough += parsePassThroughRules(stream)
            }
        }
        return GoSerializedTaintConfig(passThrough = passThrough)
    }

    internal fun parsePassThroughRules(stream: InputStream): List<GoSerializedRule.PassThrough> {
        val yaml = Yaml(configuration = YamlConfiguration(codePointLimit = Int.MAX_VALUE))
        val text = stream.bufferedReader(Charsets.UTF_8).readText()
        val root = runCatching { yaml.parseToYamlNode(text) }.getOrNull() ?: return emptyList()
        val rootMap = root as? YamlMap ?: return emptyList()
        val passNode = rootMap.field("passThrough") as? YamlList ?: return emptyList()

        return passNode.items.flatMap { it.toPassThroughRules() }
    }
}

private fun YamlMap.field(name: String): YamlNode? =
    entries.entries.firstOrNull { it.key.content == name }?.value

private const val BUILTIN_PACKAGE = "<builtin>"

private fun YamlNode.toPassThroughRules(): List<GoSerializedRule.PassThrough> {
    val map = this as? YamlMap ?: return emptyList()
    val function = (map.field("function") as? YamlMap)?.toGoFunction() ?: return emptyList()

    val copyList = map.field("copy") as? YamlList ?: return emptyList()
    val actions = copyList.items.mapNotNull { it.toPassAction() }
    if (actions.isEmpty()) return emptyList()

    // For receiver methods the engine's qualified name is `($recvType).$method`,
    // where `$recvType` is the call-site displayName — includes a leading `*`
    // for pointer receivers and omits it for value receivers. Emit both forms
    // so the rule fires regardless of how the call site spells the receiver.
    val pkgNames = if (function.receiver) {
        val typeName = function.type ?: return emptyList()
        listOf(
            "(${function.`package`}.${typeName})",
            "(*${function.`package`}.${typeName})",
        )
    } else if (function.`package` == BUILTIN_PACKAGE) {
        listOf("")
    } else {
        listOf(function.`package`)
    }

    return pkgNames.map { pkgName ->
        GoSerializedRule.PassThrough(
            pkg = GoNameMatcher.Simple(pkgName),
            function = GoNameMatcher.Simple(function.name),
            copy = actions,
        )
    }
}

private data class GoConfigFunction(
    val `package`: String,
    val type: String?,
    val name: String,
    val receiver: Boolean,
)

private fun YamlMap.toGoFunction(): GoConfigFunction? {
    val pkg = (field("package") as? YamlScalar)?.content ?: return null
    val name = (field("name") as? YamlScalar)?.content ?: return null
    val type = (field("type") as? YamlScalar)?.content
    val receiver = (field("receiver") as? YamlScalar)?.toBoolean() ?: false
    return GoConfigFunction(pkg, type, name, receiver)
}

private fun YamlNode.toPassAction(): GoSerializedPassAction? {
    val map = this as? YamlMap ?: return null
    val from = map.field("from")?.toPositionBaseWithModifiers() ?: return null
    val to = map.field("to")?.toPositionBaseWithModifiers() ?: return null
    return GoSerializedPassAction(from = from, to = to)
}

private fun YamlNode.toPositionBaseWithModifiers(): PositionBaseWithModifiers? {
    return when (this) {
        is YamlScalar -> {
            val (base, tupleSlot) = resolveResultPositionBase(content)
            createPosition(base, listOfNotNull(tupleSlot))
        }

        is YamlList -> {
            val strings = items.mapNotNull { (it as? YamlScalar)?.content }
            if (strings.size != items.size || strings.isEmpty()) {
                return null
            }

            val (base, tupleSlot) = resolveResultPositionBase(strings.first())
            val parsed = strings.drop(1).flatMap { parseGoPositionModifier(it) }
            val mods = listOfNotNull(tupleSlot) + parsed
            createPosition(base, mods)
        }

        else -> null
    }
}

private fun createPosition(base: PositionBase, modifiers: List<PositionModifier>): PositionBaseWithModifiers {
    if (modifiers.isEmpty()) {
        return PositionBaseWithModifiers.BaseOnly(base)
    }
    return PositionBaseWithModifiers.WithModifiers(base, modifiers)
}

private val fieldPattern = Regex("""\.([^#]+)#([^#]+)""")

// Pseudo-field "members" that are container element selectors rather than real
// struct fields; all collapse to the engine's single element accessor.
private val elementMembers = setOf("<element>", "<value>", "<key>")

private fun parseGoPositionModifier(str: String): List<PositionModifier> {
    val fieldParts = fieldPattern.matchEntire(str)
        ?: return listOf(PositionModifier.deserialize(str))

    val (_, member) = fieldParts.destructured
    if (member == "<deref>") {
        // `<pointer>#<deref>` is the identity accessor: the deref carries the
        // whole-value fact, so there is no accessor to apply. Drop it without
        // failing the position.
        return emptyList()
    }
    if (member in elementMembers) {
        // Element selectors collapse to the engine's single element accessor;
        // the type/class component is intentionally ignored for element selectors.
        return listOf(PositionModifier.ArrayElement)
    }

    val fieldWithType= "$str#?"
    return listOf(PositionModifier.deserialize(fieldWithType))
}

private val resultSlotPattern = Regex("""result\(([0-9]+)\)""")

private fun resolveResultPositionBase(str: String): Pair<PositionBase, PositionModifier.Field?> {
    val match = resultSlotPattern.matchEntire(str)
    if (match != null) {
        val slot = match.groupValues[1].toInt()
        return PositionBase.Result to PositionModifier.Field("tuple", "\$$slot", "?")
    }
    val normalised = if (str == "result(*)") "result" else str
    return PositionBase.deserialize(normalised) to null
}

fun loadGoSerializedTaintConfig(stream: InputStream): GoSerializedTaintConfig {
    val passThrough = GoConfigLoader.parsePassThroughRules(stream)
    return GoSerializedTaintConfig(passThrough = passThrough)
}

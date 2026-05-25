package org.opentaint.go.config

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.YamlList
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.YamlScalar
import org.opentaint.dataflow.configuration.go.serialized.GoFunctionMatcher
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

    private fun parsePassThroughRules(stream: InputStream): List<GoSerializedRule.PassThrough> {
        val yaml = Yaml(configuration = YamlConfiguration(codePointLimit = Int.MAX_VALUE))
        val text = stream.bufferedReader(Charsets.UTF_8).readText()
        val root = runCatching { yaml.parseToYamlNode(text) }.getOrNull() ?: return emptyList()
        val rootMap = root as? YamlMap ?: return emptyList()
        val passNode = rootMap.field("passThrough") as? YamlList ?: return emptyList()

        return passNode.items.mapNotNull { it.toPassThroughRule() }
    }
}

private fun YamlMap.field(name: String): YamlNode? =
    entries.entries.firstOrNull { it.key.content == name }?.value

private fun YamlNode.toPassThroughRule(): GoSerializedRule.PassThrough? {
    val map = this as? YamlMap ?: return null
    val function = (map.field("function") as? YamlMap)?.toGoFunction() ?: return null
    if (function.receiver) return null // v1: skip receiver-method rules

    val copyList = map.field("copy") as? YamlList ?: return null
    val actions = copyList.items.mapNotNull { it.toPassAction() }
    if (actions.isEmpty()) return null

    return GoSerializedRule.PassThrough(
        function = GoFunctionMatcher.Simple("${function.`package`}.${function.name}"),
        copy = actions,
    )
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

private fun YamlNode.toPositionBaseWithModifiers(): PositionBaseWithModifiers? = when (this) {
    is YamlScalar -> parseGoPositionScalar(content)?.let { PositionBaseWithModifiers.BaseOnly(it) }
    is YamlList -> {
        val strings = items.mapNotNull { (it as? YamlScalar)?.content }
        if (strings.size != items.size || strings.isEmpty()) {
            null
        } else {
            val base = parseGoPositionScalar(strings.first())
            val mods = strings.drop(1).mapNotNull { parseGoPositionModifier(it) }
            if (base == null || mods.size != strings.size - 1) null
            else PositionBaseWithModifiers.WithModifiers(base, mods)
        }
    }
    else -> null
}

// The bundled go-config writes ArrayElement as `.[*]` (with a leading dot) but
// the shared deserializer accepts only `[*]`. Normalise the Go-flavoured form
// here so the bundled passthrough rules for `fmt.Sprintf`, `strings.Join`, …
// actually load. AnyField is similarly tolerant.
private fun parseGoPositionModifier(str: String): PositionModifier? {
    val normalised = when (str) {
        ".[*]" -> "[*]"
        else -> str
    }
    return runCatching { PositionModifier.deserialize(normalised) }.getOrNull()
}

private fun parseGoPositionScalar(str: String): PositionBase? {
    // Multi-return slots like `result(0)` are not yet modelled by the Go engine.
    if (str.startsWith("result(")) return null
    // `this` belongs to receiver-method rules which we skip at the rule level.
    if (str == "this") return null
    return runCatching { PositionBase.deserialize(str) }.getOrNull()
}

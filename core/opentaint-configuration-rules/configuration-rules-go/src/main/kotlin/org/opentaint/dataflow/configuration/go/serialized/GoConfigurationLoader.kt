package org.opentaint.dataflow.configuration.go.serialized

import com.charleskorn.kaml.YamlList
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.YamlScalar
import org.opentaint.dataflow.configuration.ConfigurationLoader
import org.opentaint.dataflow.configuration.LoadedModels
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBase
import org.opentaint.dataflow.configuration.jvm.serialized.PositionBaseWithModifiers
import org.opentaint.dataflow.configuration.jvm.serialized.PositionModifier

class GoConfigurationLoader : ConfigurationLoader<GoSerializedTaintConfig> {
    override val language: String get() = "go"

    override fun load(node: YamlNode): GoSerializedTaintConfig = loadModels(node).config

    override fun loadModels(node: YamlNode): LoadedModels<GoSerializedTaintConfig> {
        val warnings = mutableListOf<String>()
        val entries = parsePassRules(node) { warnings += it }
        return LoadedModels(GoSerializedTaintConfig(passThrough = entries.flatten()), entries.size, warnings)
    }

    override fun join(config: List<GoSerializedTaintConfig>) = GoSerializedTaintConfig(
        globalSource = config.flatMap { it.globalSource },
        fieldSource = config.flatMap { it.fieldSource },
        source = config.flatMap { it.source },
        sink = config.flatMap { it.sink },
        passThrough = config.flatMap { it.passThrough },
        cleaner = config.flatMap { it.cleaner },
    )

    private fun parsePassRules(
        node: YamlNode,
        warn: (String) -> Unit,
    ): List<List<GoSerializedRule.PassThrough>> {
        val passNode = (node as? YamlMap)?.field("passThrough") as? YamlList ?: return emptyList()
        return passNode.items.mapIndexedNotNull { i, item ->
            item.toPassThroughRules { reason -> warn("passThrough[$i] dropped: $reason") }
        }
    }

    private fun YamlNode.toPassThroughRules(dropped: (String) -> Unit): List<GoSerializedRule.PassThrough>? {
        fun drop(reason: String): Nothing? {
            dropped(reason)
            return null
        }

        val map = this as? YamlMap ?: return drop("not a map")
        val functionMap = map.field("function") as? YamlMap ?: return drop("no function")
        val function = functionMap.toGoFunction(::drop) ?: return null

        val copyList = map.field("copy") as? YamlList ?: return drop("no copy")
        val actions = copyList.items.mapNotNull { it.toPassAction() }
        if (actions.isEmpty()) return drop("no copy with a valid from and to")

        // For receiver methods the engine's qualified name is `($recvType).$method`,
        // where `$recvType` is the call-site displayName — includes a leading `*`
        // for pointer receivers and omits it for value receivers. Emit both forms
        // so the rule fires regardless of how the call site spells the receiver.
        val pkgNames = if (function.receiver) {
            val typeName = function.type ?: return drop("no function.type for a receiver method")
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

    private fun YamlMap.field(name: String): YamlNode? =
        entries.entries.firstOrNull { it.key.content == name }?.value

    private fun YamlMap.toGoFunction(drop: (String) -> Nothing?): GoConfigFunction? {
        val pkg = (field("package") as? YamlScalar)?.content ?: return drop("no function.package")
        val name = (field("name") as? YamlScalar)?.content ?: return drop("no function.name")
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

        val fieldWithType = "$str#?"
        return listOf(PositionModifier.deserialize(fieldWithType))
    }

    private fun resolveResultPositionBase(str: String): Pair<PositionBase, PositionModifier.Field?> {
        val match = resultSlotPattern.matchEntire(str)
        if (match != null) {
            val slot = match.groupValues[1].toInt()
            return PositionBase.Result to PositionModifier.Field("tuple", "\$$slot", "?")
        }
        val normalised = if (str == "result(*)") "result" else str
        return PositionBase.deserialize(normalised) to null
    }

    companion object {
        private const val BUILTIN_PACKAGE = "<builtin>"
        private val resultSlotPattern = Regex("""result\(([0-9]+)\)""")

        private val fieldPattern = Regex("""\.([^#]+)#([^#]+)""")

        // Pseudo-field "members" that are container element selectors rather than real
        // struct fields; all collapse to the engine's single element accessor.
        private val elementMembers = setOf("<element>", "<value>", "<key>")
    }
}

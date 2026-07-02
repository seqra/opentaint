package org.opentaint.dataflow.configuration

import com.charleskorn.kaml.Yaml
import com.charleskorn.kaml.YamlConfiguration
import com.charleskorn.kaml.YamlMap
import com.charleskorn.kaml.YamlNode
import com.charleskorn.kaml.parseToYamlNode
import java.io.InputStream

interface ConfigurationLoader<Rules> {
    val language: String

    fun load(node: YamlNode): Rules
    fun join(config: List<Rules>): Rules

    fun load(stream: InputStream): Rules? {
        val node = yaml.parseToYamlNode(stream) as? YamlMap ?: return null
        val configLanguage = node.getScalar("language") ?: return null
        if (configLanguage.content != language) return null
        return load(node)
    }

    companion object {
        val yaml = Yaml(configuration = YamlConfiguration(codePointLimit = Int.MAX_VALUE))
    }
}

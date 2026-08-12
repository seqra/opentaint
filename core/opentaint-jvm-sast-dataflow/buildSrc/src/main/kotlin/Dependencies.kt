@file:Suppress("ConstPropertyName")

import org.opentaint.common.dep

object Versions {
    const val fastutil = "8.5.13"
}

object Libs {
    val fastutil = dep(
        group = "it.unimi.dsi",
        name = "fastutil-core",
        version = Versions.fastutil,
    )
}

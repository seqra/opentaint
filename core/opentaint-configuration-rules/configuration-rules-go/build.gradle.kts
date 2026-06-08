import org.opentaint.common.KotlinDependency

plugins {
    id("kotlin-conventions")
    kotlinSerialization()
}

dependencies {
    api(project(":configuration-rules-common"))
    api(project(":configuration-rules-jvm"))

    implementation(KotlinDependency.Libs.kotlinx_serialization_core)
    implementation(KotlinDependency.Libs.kaml)
}

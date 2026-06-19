import org.opentaint.common.KotlinDependency

plugins {
    id("kotlin-conventions")
}

dependencies {
    implementation(project(":opentaint-ir-api-jvm"))
    implementation(project(":opentaint-ir-core"))
    implementation(KotlinDependency.Libs.kotlin_logging)
//    implementation(Libs.jooq)

    testImplementation(testFixtures(project(":opentaint-ir-core")))
    testImplementation(testFixtures(project(":opentaint-ir-storage")))
//    testRuntimeOnly(Libs.guava)
}

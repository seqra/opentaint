import OpentaintIrDependency.opentaint_ir_api_common
import org.opentaint.common.KotlinDependency

plugins {
    id("kotlin-conventions")
}

dependencies {
    implementation(KotlinDependency.Libs.kaml)
    implementation(opentaint_ir_api_common)
}

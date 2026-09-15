import org.opentaint.common.KotlinDependency

plugins {
    id("kotlin-conventions")
    id("com.google.protobuf") version "0.9.4"
}

dependencies {
    api(project(":python:opentaint-ir-api-python"))

    // gRPC + Protobuf
    implementation("io.grpc:grpc-netty-shaded:1.69.0")
    implementation("io.grpc:grpc-protobuf:1.69.0")
    implementation("io.grpc:grpc-stub:1.69.0")
    implementation("com.google.protobuf:protobuf-java:4.29.3")

    implementation(KotlinDependency.Libs.kotlin_logging)

    // Required for javax.annotation used by generated gRPC stubs
    compileOnly("org.apache.tomcat:annotations-api:6.0.53")
}

protobuf {
    protoc {
        artifact = "com.google.protobuf:protoc:4.29.3"
    }
    plugins {
        create("grpc") {
            artifact = "io.grpc:protoc-gen-grpc-java:1.69.0"
        }
    }
    generateProtoTasks {
        all().forEach {
            it.plugins {
                create("grpc")
            }
        }
    }
}

sourceSets {
    main {
        proto {
            srcDir("${project.parent?.projectDir}/pir_server/proto")
        }
    }
}

tasks.named("generateProto") {
    mustRunAfter(":python:generatePirProtoStubs")
}

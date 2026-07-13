rootProject.name = "opentaint-jvm-sast-dataflow"

include("dataflow-approximations")
project(":dataflow-approximations").projectDir = file("../../model/java/dataflow")

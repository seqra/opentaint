import org.gradle.api.Project
import org.opentaint.common.OpentaintDependency

object OpentaintUtilDependency : OpentaintDependency {
    val Project.opentaintUtilCli: String
            get() = propertyDep(group = "org.opentaint.utils", name = "cli-util")
}

package security.commandinjection;

import org.apache.tools.ant.taskdefs.Execute;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;
import org.springframework.web.bind.annotation.RestController;

/**
 * Spring MVC samples for command injection via Apache Ant Execute.
 */
public class AntCommandInjectionSamples {

    @RestController
    public static class UnsafeAntExecuteController {

        @GetMapping("/command-injection/ant/run-command")
        public String unsafeRunCommand(@RequestParam("cmd") String cmd) throws Exception {
            // VULNERABLE: passing user-controlled command array to Execute.runCommand
            String[] command = new String[]{"sh", "-c", cmd};
            Execute.runCommand(null, command);
            return "executed";
        }
    }
}

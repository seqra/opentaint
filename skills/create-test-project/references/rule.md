# Rule test project

## Samples

- `@PositiveRuleSample` — reproduce the vulnerability from the requirements: tainted input from the real source flowing through the real hops into the dangerous sink, mirroring the actual signatures and annotations
- `@NegativeRuleSample` — a flow the rule must not flag: the safe (sanitized or parameterized) version of the same operation, or a confirmed false positive you're narrowing the rule against. Keep it realistic, not stripped to constants

```java
package test;

import org.opentaint.sast.test.util.PositiveRuleSample;
import org.opentaint.sast.test.util.NegativeRuleSample;
import javax.servlet.http.HttpServletRequest;
import java.sql.Connection;
import java.sql.Statement;

public class MyVulnTest {
    private Connection db;

    @PositiveRuleSample(value = "java/security/my-vuln.yaml", id = "my-vulnerability")
    public void vulnerable(HttpServletRequest req) throws Exception {
        String input = req.getParameter("id");
        Statement stmt = db.createStatement();
        stmt.executeQuery("SELECT * FROM users WHERE id = " + input);
    }

    @NegativeRuleSample(value = "java/security/my-vuln.yaml", id = "my-vulnerability")
    public void safe(HttpServletRequest req) throws Exception {
        String input = req.getParameter("id");
        var pstmt = db.prepareStatement("SELECT * FROM users WHERE id = ?");
        pstmt.setString(1, input);
        pstmt.executeQuery();
    }
}
```

## Suppress-FP

When narrowing a rule after triage confirms a false positive, add that FP as a `@NegativeRuleSample` and pin every confirmed true positive as a `@PositiveRuleSample`, so the rule edit can't silently drop a real finding. Then recompile

## Spring-entry flows

If the flow only fires through a Spring entry point (controller → bean → sink), a plain method sample will be a `falseNegative`. Use the multi-module Spring layout — read `spring-multimodule.md` and follow it

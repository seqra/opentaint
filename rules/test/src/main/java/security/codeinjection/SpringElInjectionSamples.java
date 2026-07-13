package security.codeinjection;

import org.springframework.expression.EvaluationContext;
import org.springframework.expression.Expression;
import org.springframework.expression.ExpressionParser;
import org.springframework.expression.spel.standard.SpelExpressionParser;
import org.springframework.expression.spel.support.StandardEvaluationContext;
import org.springframework.stereotype.Controller;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RequestParam;

/**
 * Spring-based samples for SpEL injection rules.
 */
public class SpringElInjectionSamples {

    @Controller
    public static class UnsafeSpringElController {

        private final ExpressionParser parser = new SpelExpressionParser();

        /**
         * Unsafe endpoint: evaluates arbitrary SpEL provided by the user.
         */
        @GetMapping("/code-injection/spring-el/unsafe")
        public String evalUnsafe(@RequestParam("expr") String expr) {
            Expression expression = parser.parseExpression(expr);
            Object result = expression.getValue();
            return String.valueOf(result);
        }
    }

    @Controller
    public static class SafeSpringElController {

        private final ExpressionParser parser = new SpelExpressionParser();

        /**
         * Safe endpoint: uses a static expression and binds user data as a variable in a constrained context.
         */
        @GetMapping("/code-injection/spring-el/safe")
        public String evalSafe(@RequestParam(value = "name", required = false) String name) {
            if (name == null) {
                name = "";
            }

            EvaluationContext ctx = new StandardEvaluationContext();
            ctx.setVariable("name", name);

            String template = "'Hello ' + #name";
            Expression expression = parser.parseExpression(template);
            Object result = expression.getValue(ctx);
            return String.valueOf(result);
        }
    }
}

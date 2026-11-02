package issues;

import base.RuleSample;
import base.RuleSet;

/**
 * Repro: taint is lost when an element of a tainted array is itself an array
 * that is later indexed (array-of-arrays / Object[] holding a String[]).
 *
 * The source marks the returned {@code Object[]} with element-level taint
 * ({@code args[*]}). Reading a scalar element ({@code args[0]}) keeps the taint
 * (see {@link PositiveScalarElementControl}), but reading an element that is
 * itself an array and then indexing that inner array
 * ({@code ((String[]) args[1])[0]}) drops it: the engine transfers the source's
 * element path to a reference fact on the destination ({@code types.$}) instead
 * of a nested element fact ({@code types[*]}), so the inner element read is not
 * considered tainted.
 *
 * This is the shape of Apache Dubbo's GenericFilter provider path:
 *   String[] parameterTypes = (String[]) invocation.getArguments()[1];
 *   ... ReflectUtils.name2class(parameterTypes[i]) ...
 */
@RuleSet("issues/issue98.yaml")
public abstract class issue98 implements RuleSample {

    Object[] src() {
        return new Object[] {"", new String[] {""}};
    }

    void sink(String data) {}

    /**
     * Control: scalar element of a tainted array reaches the sink. This already
     * works today and anchors that the source/sink/element-read all function;
     * the only difference from the failing case is that the element here is a
     * scalar, not a nested array.
     */
    static class PositiveScalarElementControl extends issue98 {
        @Override
        public void entrypoint() {
            Object[] args = src();
            String name = (String) args[0];
            sink(name);
        }
    }

    /**
     * False negative: the element {@code args[1]} is itself a {@code String[]};
     * indexing it ({@code types[0]}) loses the taint. Expected: a finding at the
     * {@code sink(types[0])} call. Observed: none.
     */
    static class PositiveNestedArrayElement extends issue98 {
        @Override
        public void entrypoint() {
            Object[] args = src();
            String[] types = (String[]) args[1];
            sink(types[0]);
        }
    }
}

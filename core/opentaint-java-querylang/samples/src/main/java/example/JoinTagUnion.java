package example;

import base.RuleSample;
import base.RuleSet;

@RuleSet("example/JoinTagUnion.yaml")
public abstract class JoinTagUnion implements RuleSample {

    static Object srcA() { return null; }
    static Object srcB() { return null; }
    static void sinkX(Object v) {}
    static void sinkY(Object v) {}

    /** Positive: source A into sink X. */
    static class PositiveAtoX extends JoinTagUnion {
        @Override public void entrypoint() {
            Object a = srcA();
            sinkX(a);
        }
    }

    /** Positive: source B into sink Y (second tag-expanded source, second sink). */
    static class PositiveBtoY extends JoinTagUnion {
        @Override public void entrypoint() {
            Object b = srcB();
            sinkY(b);
        }
    }

    /** Positive: source A into sink Y (cross-path; proves the tag union is not source-paired). */
    static class PositiveAtoY extends JoinTagUnion {
        @Override public void entrypoint() {
            Object v = srcA();
            sinkY(v);
        }
    }

    /** Positive: source B into sink X (cross-path; proves the tag union is not source-paired). */
    static class PositiveBtoX extends JoinTagUnion {
        @Override public void entrypoint() {
            Object v = srcB();
            sinkX(v);
        }
    }

    /** Negative: untainted value into a sink. */
    static class NegativeCleanIntoSink extends JoinTagUnion {
        @Override public void entrypoint() {
            Object c = "safe";
            sinkX(c);
        }
    }

    /** Negative: tainted source never reaches a sink. */
    static class NegativeNoSink extends JoinTagUnion {
        @Override public void entrypoint() {
            Object a = srcA();
            System.out.println(a);
        }
    }
}

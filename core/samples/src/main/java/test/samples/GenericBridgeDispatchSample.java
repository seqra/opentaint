package test.samples;

public class GenericBridgeDispatchSample {
    public static class Base {
    }

    public static class Left extends Base {
        Object payload;
    }

    public static class Right extends Base {
        Object payload;
    }

    public abstract static class Validator<T extends Base> {
        public void validate(T value) {
            validateImpl(value);
        }

        protected abstract void validateImpl(T value);
    }

    public static class LeftValidator extends Validator<Left> {
        @Override
        protected void validateImpl(Left value) {
        }
    }

    public static class RightValidator extends Validator<Right> {
        @Override
        protected void validateImpl(Right value) {
            sink(source());
        }
    }

    public static void incompatibleBridgeMustNotReturn(Validator<Left> validator) {
        Left value = new Left();
        validator.validate(value);
    }

    public static void compatibleBridgeMustReach(Validator<Right> validator) {
        Right value = new Right();
        validator.validate(value);
    }

    private static Object source() {
        return new Object();
    }

    private static void sink(Object value) {
    }
}

package test.samples;

public class TracePremiseCartesianSample {
    private static void sink(String value) {
    }

    public static void entryOne(String first, String second, boolean chooseFirst) {
        multipleOriginsOne(first, second, chooseFirst);
    }

    private static void multipleOriginsOne(String first, String second, boolean chooseFirst) {
        String selected = chooseFirst ? first : second;
        consumeOne(selected);
    }

    private static void consumeOne(String selected) {
        sink(selected);
    }

    public static void entry(
            String firstLeft,
            String secondLeft,
            String firstRight,
            String secondRight,
            boolean chooseLeft,
            boolean chooseRight) {
        multipleOrigins(firstLeft, secondLeft, firstRight, secondRight, chooseLeft, chooseRight);
    }

    private static void multipleOrigins(
            String firstLeft,
            String secondLeft,
            String firstRight,
            String secondRight,
            boolean chooseLeft,
            boolean chooseRight) {
        String left;
        if (chooseLeft) {
            left = firstLeft;
        } else {
            left = secondLeft;
        }

        String right;
        if (chooseRight) {
            right = firstRight;
        } else {
            right = secondRight;
        }

        consume(left, right);
    }

    private static void consume(String left, String right) {
        sink(left);
        sink(right);
    }

    public static void entryThree(
            String firstLeft,
            String secondLeft,
            String firstMiddle,
            String secondMiddle,
            String firstRight,
            String secondRight,
            boolean chooseLeft,
            boolean chooseMiddle,
            boolean chooseRight) {
        multipleOriginsThree(
                firstLeft,
                secondLeft,
                firstMiddle,
                secondMiddle,
                firstRight,
                secondRight,
                chooseLeft,
                chooseMiddle,
                chooseRight);
    }

    private static void multipleOriginsThree(
            String firstLeft,
            String secondLeft,
            String firstMiddle,
            String secondMiddle,
            String firstRight,
            String secondRight,
            boolean chooseLeft,
            boolean chooseMiddle,
            boolean chooseRight) {
        String left = chooseLeft ? firstLeft : secondLeft;
        String middle = chooseMiddle ? firstMiddle : secondMiddle;
        String right = chooseRight ? firstRight : secondRight;
        consumeThree(left, middle, right);
    }

    private static void consumeThree(String left, String middle, String right) {
        sink(left);
        sink(middle);
        sink(right);
    }
}

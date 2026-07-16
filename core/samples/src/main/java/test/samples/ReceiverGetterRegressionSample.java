package test.samples;

public class ReceiverGetterRegressionSample {
    private static Owner source() {
        return null;
    }

    public static void sink(String value) {
    }

    public void wholeReceiverThroughGetter(Owner owner) {
        owner = source();
        sink(owner.getId());
    }

    public static class Owner {
        private String id;

        public String getId() {
            return this.id;
        }
    }
}

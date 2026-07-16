package test.samples;

public class ReceiverGetterRegressionSample {
    private static Owner source() {
        return null;
    }

    public static void sink(Integer value) {
    }

    public void wholeReceiverThroughGetter(Owner owner) {
        owner = source();
        sink(owner.getId());
    }

    public static class Owner {
        private Integer id;

        public Integer getId() {
            return this.id;
        }
    }
}

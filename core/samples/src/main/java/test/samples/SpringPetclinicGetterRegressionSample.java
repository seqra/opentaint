package test.samples;

import org.springframework.web.bind.annotation.PostMapping;

public class SpringPetclinicGetterRegressionSample {
    public static void sink(Integer value) {
    }

    @PostMapping
    public void wholeReceiverThroughGetter(Owner owner) {
        sink(owner.getId());
    }

    public static class Owner {
        private Integer id;

        public Integer getId() {
            return this.id;
        }
    }
}

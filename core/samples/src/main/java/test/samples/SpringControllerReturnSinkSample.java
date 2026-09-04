package test.samples;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class SpringControllerReturnSinkSample {
    @GetMapping
    public String returnDirect(String value) {
        return value;
    }

    @GetMapping
    public String returnStringGetter(Owner owner) {
        return owner.getName();
    }

    @GetMapping
    public String returnBoxedGetterValueOf(Owner owner) {
        return String.valueOf(owner.getId());
    }

    @GetMapping
    public String returnBoxedGetterToString(Owner owner) {
        return owner.getId().toString();
    }

    public static class BaseEntity {
        private Integer id;

        private String name;

        public Integer getId() {
            return this.id;
        }

        public String getName() {
            return this.name;
        }
    }

    public static final class Owner extends BaseEntity {
    }
}

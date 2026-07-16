package test.samples;

public class BaseOnlyGetterFuzzSample {
    private static <T> T source() {
        return null;
    }

    public static void sink(Integer value) {
    }

    private static Integer identity(Integer value) {
        return value;
    }

    private static Integer identityTwice(Integer value) {
        return identity(value);
    }

    private static Integer extract(Owner owner) {
        return owner.getId();
    }

    private static Integer extractViaLocal(Owner owner) {
        Integer value = owner.getId();
        return value;
    }

    private static Integer choose(boolean first, Integer left, Integer right) {
        return first ? left : right;
    }

public void directGetter(Owner owner) {
        owner = source();
        sink(owner.getId());
    }

    public void getterIntoLocal(Owner owner) {
        owner = source();
        Integer value = owner.getId();
        sink(value);
    }

    public void getterWithReassignment(Owner owner) {
        owner = source();
        Integer value = null;
        value = owner.getId();
        sink(value);
    }

    public void getterThroughIdentity(Owner owner) {
        owner = source();
        sink(identity(owner.getId()));
    }

    public void getterThroughTwoCalls(Owner owner) {
        owner = source();
        sink(identityTwice(owner.getId()));
    }

    public void getterInCallee(Owner owner) {
        owner = source();
        sink(extract(owner));
    }

    public void getterAndLocalInCallee(Owner owner) {
        owner = source();
        sink(extractViaLocal(owner));
    }

    public void getterAfterReceiverAlias(Owner owner) {
        owner = source();
        Owner alias = owner;
        sink(alias.getId());
    }

    public void getterAfterTwoReceiverAliases(Owner owner) {
        owner = source();
        Owner first = owner;
        Owner second = first;
        sink(second.getId());
    }

    public void getterInIfThen(Owner owner) {
        owner = source();
        if (owner != null) {
            sink(owner.getId());
        }
    }

    public void getterAfterIfAssignment(Owner owner) {
        owner = source();
        Integer value = null;
        if (owner != null) {
            value = owner.getId();
        }
        sink(value);
    }

    public void getterInTernary(Owner owner) {
        owner = source();
        Integer value = owner != null ? owner.getId() : null;
        sink(value);
    }

    public void getterAsTernaryArm(Owner owner) {
        owner = source();
        sink(choose(owner != null, owner.getId(), null));
    }

    public void getterInSwitch(Owner owner) {
        owner = source();
        Integer value = null;
        switch (owner.getMode()) {
            case 0:
                value = owner.getId();
                break;
            default:
                break;
        }
        sink(value);
    }

    public void getterInForLoop(Owner owner) {
        owner = source();
        Integer value = null;
        for (int i = 0; i < 1; i++) {
            value = owner.getId();
        }
        sink(value);
    }

    public void getterInWhileLoop(Owner owner) {
        owner = source();
        Integer value = null;
        int i = 0;
        while (i++ < 1) {
            value = owner.getId();
        }
        sink(value);
    }

    public void getterInDoWhileLoop(Owner owner) {
        owner = source();
        Integer value;
        do {
            value = owner.getId();
        } while (false);
        sink(value);
    }

    public void getterInTry(Owner owner) {
        owner = source();
        Integer value = null;
        try {
            value = owner.getId();
        } finally {
            sink(value);
        }
    }

    public void getterInSynchronized(Owner owner) {
        owner = source();
        synchronized (this) {
            sink(owner.getId());
        }
    }

    public void nestedGetter(Owner owner) {
        owner = source();
        sink(owner.getProfile().getId());
    }

    public void nestedGetterViaLocal(Owner owner) {
        owner = source();
        Profile profile = owner.getProfile();
        sink(profile.getId());
    }

    public void nestedGetterAndValueLocal(Owner owner) {
        owner = source();
        Profile profile = owner.getProfile();
        Integer value = profile.getId();
        sink(value);
    }

    public void nestedGetterThroughIdentity(Owner owner) {
        owner = source();
        sink(identity(owner.getProfile().getId()));
    }

    public void nestedPublicField(Owner owner) {
        owner = source();
        sink(owner.getProfile().publicId);
    }

    public void nestedFieldViaLocal(Owner owner) {
        owner = source();
        Profile profile = owner.getProfile();
        sink(profile.publicId);
    }

    public void getterReturningFieldViaLocal(LocalGetterOwner owner) {
        owner = source();
        sink(owner.getId());
    }

    public void getterReturningConditionalField(ConditionalGetterOwner owner) {
        owner = source();
        sink(owner.getId());
    }

    public void getterDelegatingToPrivateMethod(DelegatingOwner owner) {
        owner = source();
        sink(owner.getId());
    }

    public void inheritedGetter(DerivedOwner owner) {
        owner = source();
        sink(owner.getId());
    }

    public void overriddenGetter(OverridingOwner owner) {
        owner = source();
        sink(owner.getId());
    }

    public void getterFromInterfaceImplementation(InterfaceOwner owner) {
        owner = source();
        HasId value = owner;
        sink(value.getId());
    }

    public void getterAfterReceiverIdentity(Owner owner) {
        owner = source();
        sink(owner.self().getId());
    }

    public void getterAfterTwoReceiverMethods(Owner owner) {
        owner = source();
        sink(owner.self().self().getId());
    }

    public void getterFromArrayField(ArrayOwner owner) {
        owner = source();
        sink(owner.getFirstId());
    }

    public void getterFromNestedArray(ArrayOwner owner) {
        owner = source();
        sink(owner.getIds()[0]);
    }

    public void getterStoredInFreshBox(Owner owner) {
        owner = source();
        Box box = new Box(owner.getId());
        sink(box.value);
    }

    public void getterStoredBySetter(Owner owner) {
        owner = source();
        Box box = new Box(null);
        box.setValue(owner.getId());
        sink(box.getValue());
    }

    public void getterSelectedWithCleanValue(Owner owner) {
        owner = source();
        Integer value = choose(owner != null, owner.getId(), Integer.valueOf(0));
        sink(value);
    }

    public void twoGetterCandidates(Owner owner) {
        owner = source();
        Integer value = owner.getMode() == 0 ? owner.getId() : owner.getBackupId();
        sink(value);
    }

    public interface HasId {
        Integer getId();
    }

    public static class Owner implements HasId {
        private Integer id;
        private Integer backupId;
        private int mode;
        private Profile profile;

        @Override
        public Integer getId() {
            return this.id;
        }

        public Integer getBackupId() {
            return this.backupId;
        }

        public int getMode() {
            return this.mode;
        }

        public Profile getProfile() {
            return this.profile;
        }

        public Owner self() {
            return this;
        }
    }

    public static class Profile {
        private Integer id;
        public Integer publicId;

        public Integer getId() {
            return this.id;
        }
    }

    public static class LocalGetterOwner {
        private Integer id;

        public Integer getId() {
            Integer result = this.id;
            return result;
        }
    }

    public static class ConditionalGetterOwner {
        private Integer id;

        public Integer getId() {
            return this.id == null ? null : this.id;
        }
    }

    public static class DelegatingOwner {
        private Integer id;

        public Integer getId() {
            return readId();
        }

        private Integer readId() {
            return this.id;
        }
    }

    public static class BaseOwner {
        protected Integer id;

        public Integer getId() {
            return this.id;
        }
    }

    public static class DerivedOwner extends BaseOwner {
    }

    public static class OverridingOwner extends BaseOwner {
        @Override
        public Integer getId() {
            return super.getId();
        }
    }

    public static class InterfaceOwner implements HasId {
        private Integer id;

        @Override
        public Integer getId() {
            return this.id;
        }
    }

    public static class ArrayOwner {
        private Integer[] ids;

        public Integer getFirstId() {
            return this.ids[0];
        }

        public Integer[] getIds() {
            return this.ids;
        }
    }

    public static class Box {
        private Integer value;

        public Box(Integer value) {
            this.value = value;
        }

        public void setValue(Integer value) {
            this.value = value;
        }

        public Integer getValue() {
            return this.value;
        }
    }
}

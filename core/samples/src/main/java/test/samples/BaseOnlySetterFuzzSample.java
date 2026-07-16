package test.samples;

public class BaseOnlySetterFuzzSample {
    private static String source() {
        return "tainted";
    }

    private static void sink(String value) {
    }

    private static String identity(String value) {
        return value;
    }

    private static Box newBox() {
        return new Box();
    }

    private static Box alias(Box box) {
        return box;
    }

    private static void putPayload(Box box, String value) {
        box.setPayload(value);
    }

    private static String readPayload(Box box) {
        return box.getPayload();
    }

    public static void directUnrelatedStringSetter() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void sourceLocalThenSetter() {
        String value = source();
        Box box = new Box();
        box.setPayload(value);
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void sourceThroughIdentity() {
        Box box = new Box();
        box.setPayload(identity(source()));
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void valueAliasChain() {
        String first = source();
        String second = first;
        String third = second;
        Box box = new Box();
        box.setPayload(third);
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void receiverAliasBeforeWrite() {
        Box box = new Box();
        Box writeAlias = box;
        writeAlias.setPayload(source());
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void receiverAliasForKillingSetter() {
        Box box = new Box();
        box.setPayload(source());
        Box metadataAlias = box;
        metadataAlias.setLabel("safe");
        sink(box.getPayload());
    }

    public static void receiverAliasForRead() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        Box readAlias = box;
        sink(readAlias.getPayload());
    }

    public static void distinctAliasesForEveryOperation() {
        Box box = new Box();
        Box writer = box;
        Box metadataWriter = box;
        Box reader = box;
        writer.setPayload(source());
        metadataWriter.setLabel("safe");
        sink(reader.getPayload());
    }

    public static void castReceiverAtSetter() {
        Box box = new Box();
        box.setPayload(source());
        ((Box) box).setLabel("safe");
        sink(box.getPayload());
    }

    public static void castReceiverAtGetter() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        sink(((Box) box).getPayload());
    }

    public static void castValueBeforePayloadWrite() {
        Object value = source();
        Box box = new Box();
        box.setPayload((String) value);
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void factoryAllocatedReceiver() {
        Box box = newBox();
        box.setPayload(source());
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void receiverThroughIdentityHelper() {
        Box box = alias(new Box());
        box.setPayload(source());
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void payloadWriteThroughHelper() {
        Box box = new Box();
        putPayload(box, source());
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void payloadReadThroughHelper() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        sink(readPayload(box));
    }

    public static void writeAndReadThroughHelpers() {
        Box box = new Box();
        putPayload(box, source());
        box.setLabel("safe");
        sink(readPayload(box));
    }

    public static void twoUnrelatedStringSetters() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        box.setCategory("public");
        sink(box.getPayload());
    }

    public static void threeUnrelatedSettersMixedTypes() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        box.setCount(7);
        box.setEnabled(true);
        sink(box.getPayload());
    }

    public static void primitiveSetterKillsIdentity() {
        Box box = new Box();
        box.setPayload(source());
        box.setCount(1);
        sink(box.getPayload());
    }

    public static void booleanSetterKillsIdentity() {
        Box box = new Box();
        box.setPayload(source());
        box.setEnabled(false);
        sink(box.getPayload());
    }

    public static void nullMetadataSetter() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel(null);
        sink(box.getPayload());
    }

    public static void metadataLocalSetter() {
        Box box = new Box();
        box.setPayload(source());
        String metadata = "safe";
        box.setLabel(metadata);
        sink(box.getPayload());
    }

    public static void metadataIdentitySetter() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel(identity("safe"));
        sink(box.getPayload());
    }

    public static void overwriteMetadataTwice() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("first");
        box.setLabel("second");
        sink(box.getPayload());
    }

    public static void branchBeforeKillingSetter() {
        Box box = new Box();
        box.setPayload(source());
        if (box.getCount() == 0) {
            box.setLabel("zero");
        }
        box.setCategory("after-branch");
        sink(box.getPayload());
    }

    public static void bothBranchArmsKillIdentity() {
        Box box = new Box();
        box.setPayload(source());
        if (box.getCount() == 0) {
            box.setLabel("zero");
        } else {
            box.setCategory("nonzero");
        }
        sink(box.getPayload());
    }

    public static void branchSelectsSafeMetadata() {
        Box box = new Box();
        box.setPayload(source());
        String metadata;
        if (box.getCount() == 0) {
            metadata = "zero";
        } else {
            metadata = "nonzero";
        }
        box.setLabel(metadata);
        sink(box.getPayload());
    }

    public static void loopKillingSetter() {
        Box box = new Box();
        box.setPayload(source());
        for (int i = 0; i < 2; i++) {
            box.setCount(i);
        }
        box.setLabel("after-loop");
        sink(box.getPayload());
    }

    public static void doWhileKillingSetter() {
        Box box = new Box();
        box.setPayload(source());
        int i = 0;
        do {
            box.setCount(i++);
        } while (i < 2);
        sink(box.getPayload());
    }

    public static void arrayCarriesReceiverAlias() {
        Box box = new Box();
        box.setPayload(source());
        Box[] aliases = new Box[]{box};
        aliases[0].setLabel("safe");
        box.setCategory("after-array-alias");
        sink(box.getPayload());
    }

    public static void arrayCarriesTaintedValue() {
        String[] values = new String[]{source()};
        Box box = new Box();
        box.setPayload(values[0]);
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void holderCarriesReceiverAlias() {
        Box box = new Box();
        box.setPayload(source());
        Holder holder = new Holder(box);
        holder.box.setLabel("safe");
        box.setCategory("after-holder-alias");
        sink(box.getPayload());
    }

    public static void nestedScopeAliasesReceiver() {
        Box box = new Box();
        box.setPayload(source());
        {
            Box nested = box;
            nested.setLabel("safe");
        }
        sink(box.getPayload());
    }

    public static void sinkValueLocalAfterGetter() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        String result = box.getPayload();
        sink(result);
    }

    public static void sinkValueAliasChainAfterGetter() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        String result = box.getPayload();
        String alias = result;
        sink(alias);
    }

    public static void getterResultThroughIdentity() {
        Box box = new Box();
        box.setPayload(source());
        box.setLabel("safe");
        sink(identity(box.getPayload()));
    }

    public static void subclassReceiver() {
        ExtendedBox box = new ExtendedBox();
        box.setPayload(source());
        box.setLabel("safe");
        sink(box.getPayload());
    }

    public static void interfaceTypedReceiver() {
        PayloadAccess access = new Box();
        access.setPayload(source());
        access.setLabel("safe");
        sink(access.getPayload());
    }

    private interface PayloadAccess {
        void setPayload(String payload);
        void setLabel(String label);
        String getPayload();
    }

    private static class Box implements PayloadAccess {
        private String payload;
        private String label;
        private String category;
        private int count;
        private boolean enabled;

        public void setPayload(String payload) { this.payload = payload; }
        public String getPayload() { return payload; }
        public void setLabel(String label) { this.label = label; }
        public void setCategory(String category) { this.category = category; }
        public void setCount(int count) { this.count = count; }
        public int getCount() { return count; }
        public void setEnabled(boolean enabled) { this.enabled = enabled; }
    }

    private static final class ExtendedBox extends Box {
    }

    private static final class Holder {
        private final Box box;
        private Holder(Box box) { this.box = box; }
    }
}

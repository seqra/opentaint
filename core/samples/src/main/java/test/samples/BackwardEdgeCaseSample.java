package test.samples;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;
import java.util.function.Supplier;

public class BackwardEdgeCaseSample {

    static class Box {
        String f;
        String g;

        Box() { }

        Box(String f) {
            this.f = f;
        }

        Box(String f, String g) {
            this.f = f;
            this.g = g;
        }
    }

    static class Outer {
        Middle middle = new Middle();
        Box box;
    }

    static class Middle {
        Box box = new Box();
    }

    static class Holder {
        Box box;
    }

    static class Builder {
        private String a;
        private String b;

        Builder withA(String a) {
            this.a = a;
            return this;
        }

        Builder withB(String b) {
            this.b = b;
            return this;
        }

        Box build() {
            return new Box(a, b);
        }
    }

    static class Stateful {
        private String value;

        void set(String value) {
            this.value = value;
        }

        void reset() {
            this.value = "safe";
        }

        String get() {
            return value;
        }
    }

    interface Producer {
        String produce();
    }

    static class TaintingProducer implements Producer {
        private final BackwardEdgeCaseSample owner;

        TaintingProducer(BackwardEdgeCaseSample owner) {
            this.owner = owner;
        }

        @Override
        public String produce() {
            return owner.source();
        }
    }

    static class CleanProducer implements Producer {
        @Override
        public String produce() {
            return "safe";
        }
    }

    interface Consumer {
        void consume(String data);
    }

    static class SinkingConsumer implements Consumer {
        private final BackwardEdgeCaseSample owner;

        SinkingConsumer(BackwardEdgeCaseSample owner) {
            this.owner = owner;
        }

        @Override
        public void consume(String data) {
            owner.sink(data);
        }
    }

    static class IgnoringConsumer implements Consumer {
        private final BackwardEdgeCaseSample owner;

        IgnoringConsumer(BackwardEdgeCaseSample owner) {
            this.owner = owner;
        }

        @Override
        public void consume(String data) {
            owner.sink("safe");
        }
    }

    private static String staticValue;

    private int counter;

    public String source() { return "tainted"; }

    public void sink(String data) { }

    private boolean unknown() {
        return counter > 3;
    }

    private Box wrap(String x) {
        Box y = new Box();
        y.f = x;
        return y;
    }

    private Box wrapTwice(String x) {
        return wrap(x);
    }

    public void returnNewBoxField() {
        Box z = wrap(source());
        sink(z.f);
    }

    public void returnNewBoxOtherField() {
        Box z = wrap(source());
        sink(z.g);
    }

    public void returnNewBoxTwoLevels() {
        Box z = wrapTwice(source());
        sink(z.f);
    }

    public void returnNewBoxReassigned() {
        Box z = wrap(source());
        z = wrap("safe");
        sink(z.f);
    }

    public void returnNewBoxSeparateInstances() {
        Box tainted = wrap(source());
        Box clean = wrap("safe");
        sink(clean.f);
    }

    public void constructorStoresField() {
        Box b = new Box(source());
        sink(b.f);
    }

    public void constructorStoresOtherField() {
        Box b = new Box(source(), "safe");
        sink(b.g);
    }

    public void builderChainField() {
        Box b = new Builder().withA(source()).withB("safe").build();
        sink(b.f);
    }

    public void builderChainOtherField() {
        Box b = new Builder().withA(source()).withB("safe").build();
        sink(b.g);
    }

    private void fill(Box b, String x) {
        b.f = x;
    }

    private void clear(Box b) {
        b.f = "safe";
    }

    public void calleeFillsArgField() {
        Box b = new Box();
        fill(b, source());
        sink(b.f);
    }

    public void calleeOverwritesArgField() {
        Box b = new Box();
        b.f = source();
        clear(b);
        sink(b.f);
    }

    public void calleeOverwriteTwice() {
        Box b = new Box();
        fill(b, source());
        fill(b, "safe");
        sink(b.f);
    }

    private void fillViaLocalAlias(Box b) {
        Box t = b;
        t.f = source();
    }

    public void calleeFillsThroughLocalAlias() {
        Box b = new Box();
        fillViaLocalAlias(b);
        sink(b.f);
    }

    private String getF(Box b) {
        return b.f;
    }

    private String getG(Box b) {
        return b.g;
    }

    public void getterReturnsField() {
        Box b = new Box();
        b.f = source();
        sink(getF(b));
    }

    public void getterReturnsOtherField() {
        Box b = new Box();
        b.f = source();
        sink(getG(b));
    }

    private void writeDeep(Outer o, String x) {
        o.middle.box.f = x;
    }

    private String readDeep(Outer o) {
        return o.middle.box.f;
    }

    private String readDeepOther(Outer o) {
        return o.middle.box.g;
    }

    private void setBox(Outer o, String x) {
        o.box = new Box(x);
    }

    private String readBox(Outer o) {
        return o.box.f;
    }

    public void nestedDepth2AcrossMethods() {
        Outer o = new Outer();
        setBox(o, source());
        sink(readBox(o));
    }

    public void nestedDepth3AcrossMethods() {
        Outer o = new Outer();
        writeDeep(o, source());
        sink(readDeep(o));
    }

    public void nestedDepth3OtherLeaf() {
        Outer o = new Outer();
        writeDeep(o, source());
        sink(readDeepOther(o));
    }

    public void fieldOverwriteKill() {
        Box b = new Box();
        b.f = source();
        b.f = "safe";
        sink(b.f);
    }

    public void localReassignKill() {
        String s = source();
        s = "safe";
        sink(s);
    }

    public void unrelatedFieldWrite() {
        Box b = new Box();
        b.f = source();
        sink(b.g);
    }

    public void unrelatedObjectSameField() {
        Box a = new Box();
        Box b = new Box();
        a.f = source();
        sink(b.f);
    }

    public void localAliasWrite() {
        Box b = new Box();
        Box b2 = b;
        b2.f = source();
        sink(b.f);
    }

    public void localAliasOverwrite() {
        Box b = new Box();
        b.f = source();
        Box b2 = b;
        b2.f = "safe";
        sink(b.f);
    }

    public void heapAliasWrite() {
        Box b = new Box();
        Holder h = new Holder();
        h.box = b;
        h.box.f = source();
        sink(b.f);
    }

    public void thisFieldState() {
        Stateful s = new Stateful();
        s.set(source());
        sink(s.get());
    }

    public void thisFieldStateReset() {
        Stateful s = new Stateful();
        s.set(source());
        s.reset();
        sink(s.get());
    }

    private void writeStatic(String x) {
        staticValue = x;
    }

    private String readStatic() {
        return staticValue;
    }

    public void staticFieldAcrossMethods() {
        writeStatic(source());
        sink(readStatic());
    }

    public void staticFieldOverwritten() {
        staticValue = source();
        staticValue = "safe";
        sink(staticValue);
    }

    public void arrayWeakUpdate() {
        String[] arr = new String[2];
        arr[0] = source();
        arr[1] = "safe";
        sink(arr[0]);
    }

    public void arrayDifferentArray() {
        String[] a = new String[1];
        String[] b = new String[1];
        a[0] = source();
        sink(b[0]);
    }

    private void fillArray(String[] arr, String x) {
        arr[0] = x;
    }

    public void arrayFilledInCallee() {
        String[] arr = new String[1];
        fillArray(arr, source());
        sink(arr[0]);
    }

    public void listAddGet() {
        List<String> list = new ArrayList<>();
        list.add(source());
        sink(list.get(0));
    }

    public void listOtherList() {
        List<String> a = new ArrayList<>();
        List<String> b = new ArrayList<>();
        a.add(source());
        b.add("safe");
        sink(b.get(0));
    }

    public void stringBuilderChain() {
        StringBuilder sb = new StringBuilder();
        sb.append("a").append(source()).append("b");
        sink(sb.toString());
    }

    private String decorate(String x) {
        return "[" + x + "]";
    }

    public void stringConcatInCallee() {
        sink(decorate(source()).trim());
    }

    private String recurse(String x, int n) {
        if (n <= 0) {
            return x;
        }
        return recurse(x, n - 1);
    }

    public void recursionPassThrough() {
        sink(recurse(source(), 5));
    }

    private String recurseDropping(String x, int n) {
        if (n <= 0) {
            return "safe";
        }
        return recurseDropping(x, n - 1);
    }

    public void recursionDropsValue() {
        sink(recurseDropping(source(), 5));
    }

    public void loopShiftsValue() {
        String a = "safe";
        String b = "safe";
        String c = source();
        for (int i = 0; i < 3; i++) {
            a = b;
            b = c;
            c = "safe";
        }
        sink(a);
    }

    public void loopFieldShift() {
        Box b = new Box();
        b.g = source();
        for (int i = 0; i < 3; i++) {
            b.f = b.g;
            b.g = "safe";
        }
        sink(b.f);
    }

    public void virtualDispatchTaintingImpl() {
        Producer p = unknown() ? new TaintingProducer(this) : new CleanProducer();
        sink(p.produce());
    }

    public void virtualDispatchSinkingImpl() {
        Consumer c = unknown() ? new SinkingConsumer(this) : new IgnoringConsumer(this);
        c.consume(source());
    }

    public void lambdaCapturesTainted() {
        String data = source();
        Supplier<String> s = () -> data;
        sink(s.get());
    }

    public void lambdaReturnsSource() {
        Supplier<String> s = () -> source();
        sink(s.get());
    }

    public void lambdaIgnoresArgument() {
        Function<String, String> f = x -> "safe";
        sink(f.apply(source()));
    }

    public void lambdaPassesArgument() {
        Function<String, String> f = x -> x;
        sink(f.apply(source()));
    }

    public void ternaryMerge() {
        String s = unknown() ? source() : "safe";
        sink(s);
    }

    public void ternaryBothSafe() {
        String t = source();
        String s = unknown() ? "a" : "b";
        sink(s);
    }

    private String level2() {
        return source();
    }

    private String level1() {
        return level2();
    }

    public void sourceTwoLevelsDeep() {
        sink(level1());
    }

    private void sinkHelper(String x) {
        sink(x);
    }

    private void sinkViaParam(String x) {
        sinkHelper(x);
    }

    private void sinkIgnoringParam(String x) {
        sinkHelper("safe");
    }

    public void sinkTwoLevelsDeep() {
        sinkViaParam(source());
    }

    public void sinkInCalleeIgnoresParam() {
        sinkIgnoringParam(source());
    }

    private Box pass(Box b) {
        return b;
    }

    public void returnParamFieldAfterChain() {
        Box b = new Box();
        b.f = source();
        Box r = pass(pass(b));
        sink(r.f);
    }

    public void conditionalOverwrite() {
        Box b = new Box();
        b.f = source();
        if (unknown()) {
            b.f = "safe";
        }
        sink(b.f);
    }

    private void maybeClear(Box b) {
        if (unknown()) {
            b.f = "safe";
        }
    }

    public void conditionalOverwriteInCallee() {
        Box b = new Box();
        b.f = source();
        maybeClear(b);
        sink(b.f);
    }

    private void moveFToG(Box b) {
        b.g = b.f;
        b.f = "safe";
    }

    public void calleeMovesFieldTarget() {
        Box b = new Box();
        b.f = source();
        moveFToG(b);
        sink(b.g);
    }

    public void calleeMovesFieldSource() {
        Box b = new Box();
        b.f = source();
        moveFToG(b);
        sink(b.f);
    }

    private void copyField(Box from, Box to) {
        to.f = from.f;
    }

    public void copyFieldBetweenObjects() {
        Box a = new Box();
        Box b = new Box();
        a.f = source();
        copyField(a, b);
        sink(b.f);
    }

    public void copyFieldReversedDirection() {
        Box a = new Box();
        Box b = new Box();
        a.f = source();
        copyField(b, a);
        sink(a.f);
    }

    public void swapFields() {
        Box b = new Box();
        b.f = source();
        b.g = "safe";
        String t = b.f;
        b.f = b.g;
        b.g = t;
        sink(b.g);
    }

    public void swapFieldsKillsOld() {
        Box b = new Box();
        b.f = source();
        b.g = "safe";
        String t = b.f;
        b.f = b.g;
        b.g = t;
        sink(b.f);
    }

    private Box rewrap(Box b) {
        return new Box(b.f);
    }

    public void rewrapThroughNewObject() {
        Box b = wrap(source());
        Box r = rewrap(b);
        sink(r.f);
    }

    public void boxStoredInHolderReturned() {
        Holder h = new Holder();
        h.box = wrap(source());
        Box read = h.box;
        sink(read.f);
    }

    public void staticWrittenInCallerReadInCallee() {
        staticValue = source();
        sink(readStatic());
    }

    public void staticReadBeforeWrite() {
        staticValue = "safe";
        String s = readStatic();
        writeStatic(source());
        sink(s);
    }

    public void fieldReadBeforeWrite() {
        Box b = new Box();
        String s = b.f;
        b.f = source();
        sink(s);
    }

    private void sinkField(Box b) {
        sink(b.f);
    }

    public void sinkOnArgumentFieldInCallee() {
        Box b = new Box();
        b.f = source();
        sinkField(b);
    }

    public void sinkOnOtherArgumentFieldInCallee() {
        Box b = new Box();
        b.g = source();
        sinkField(b);
    }

    private void touchOtherField(Box b) {
        b.g = "safe";
    }

    public void calleeTouchesOtherField() {
        Box b = new Box();
        b.f = source();
        touchOtherField(b);
        sink(b.f);
    }

    private void replaceBox(Holder h) {
        h.box = new Box("safe");
    }

    public void calleeReplacesHeldBox() {
        Holder h = new Holder();
        h.box = wrap(source());
        replaceBox(h);
        sink(h.box.f);
    }

    public void oldReferenceSurvivesReplace() {
        Holder h = new Holder();
        h.box = wrap(source());
        Box old = h.box;
        replaceBox(h);
        sink(old.f);
    }

    private Outer makeOuter(String x) {
        Outer o = new Outer();
        o.box = wrap(x);
        return o;
    }

    public void nestedFactories() {
        Outer o = makeOuter(source());
        sink(o.box.f);
    }

    public void nestedFactoriesOtherLeaf() {
        Outer o = makeOuter(source());
        sink(o.box.g);
    }

    public void lambdaSinksCaptured() {
        String d = source();
        Runnable r = () -> sink(d);
        r.run();
    }

    public void lambdaSinksCapturedClean() {
        String d = source();
        String c = "safe";
        Runnable r = () -> sink(c);
        r.run();
    }

    private void forEachSink(List<String> items, java.util.function.Consumer<String> action) {
        for (String item : items) {
            action.accept(item);
        }
    }

    public void higherOrderSinkLambda() {
        List<String> items = new ArrayList<>();
        items.add(source());
        forEachSink(items, x -> sink(x));
    }

    public void knownReceiverCleanImpl() {
        Producer p = new CleanProducer();
        sink(p.produce());
    }

    public void killBetweenTwoSinks() {
        String s = source();
        sink(s);
        s = "safe";
        sink(s);
    }

    public void taintBetweenTwoSinks() {
        String s = "safe";
        sink(s);
        s = source();
        sink(s);
    }

    public void twoSinksDifferentBoxes() {
        Box a = wrap(source());
        Box b = wrap("safe");
        sink(b.f);
        sink(a.f);
    }

    private void swapArgs(Box a, Box b) {
        String t = a.f;
        a.f = b.f;
        b.f = t;
    }

    public void swapArgsReceiver() {
        Box a = new Box();
        Box b = new Box();
        a.f = source();
        swapArgs(a, b);
        sink(b.f);
    }

    public void swapArgsDonor() {
        Box a = new Box();
        Box b = new Box();
        a.f = source();
        swapArgs(a, b);
        sink(a.f);
    }

    private void clearSecondThenFillFirst(Box x, Box y, String v) {
        y.f = "safe";
        x.f = v;
    }

    public void sameObjectPassedTwice() {
        Box b = new Box();
        clearSecondThenFillFirst(b, b, source());
        sink(b.f);
    }

    public void resultAssignedToArgumentVariable() {
        Box b = new Box();
        b.f = source();
        b = pass(b);
        sink(b.f);
    }

    private Box fresh(Box b) {
        return new Box();
    }

    public void resultReplacesArgumentVariable() {
        Box b = new Box();
        b.f = source();
        b = fresh(b);
        sink(b.f);
    }

    private String self(String s) {
        return s;
    }

    public void stringResultAssignedToArgument() {
        String s = source();
        s = self(s);
        sink(s);
    }

    private void writeThenReassignParam(Box b) {
        b.f = source();
        b = new Box();
        b.f = "safe";
    }

    public void calleeReassignsParameter() {
        Box b = new Box();
        writeThenReassignParam(b);
        sink(b.f);
    }

    private String data;

    private void init() {
        this.data = source();
    }

    private void resetData() {
        this.data = "safe";
    }

    private void use() {
        sink(this.data);
    }

    public void entryThisFieldInitUse() {
        init();
        use();
    }

    public void entryThisFieldInitResetUse() {
        init();
        resetData();
        use();
    }

    private void appendTo(StringBuilder sb, String x) {
        sb.append(x);
    }

    public void libraryMutationInCallee() {
        StringBuilder sb = new StringBuilder();
        appendTo(sb, source());
        sink(sb.toString());
    }

    public void libraryMutationThroughAlias() {
        StringBuilder sb = new StringBuilder();
        StringBuilder sb2 = sb;
        sb2.append(source());
        sink(sb.toString());
    }

    public void arrayOfBoxes() {
        Box[] arr = new Box[1];
        arr[0] = new Box();
        arr[0].f = source();
        sink(arr[0].f);
    }

    private Box copyOf(Box b) {
        return new Box(b.f, b.g);
    }

    public void copyConstructorOtherField() {
        Box b = new Box();
        b.f = source();
        Box c = copyOf(b);
        sink(c.g);
    }

    public void copyConstructorField() {
        Box b = new Box();
        b.f = source();
        Box c = copyOf(b);
        sink(c.f);
    }

    public void conditionalFactoryResult() {
        Box b = unknown() ? wrap(source()) : new Box();
        sink(b.f);
    }

    private void sinkThenSpinCallee(String x) {
        sink(x);
        while (true) {
            counter++;
        }
    }

    public void calleeWithoutNormalExit() {
        sinkThenSpinCallee(source());
    }

    private void sinkThenThrow(String x) {
        sink(x);
        throw new IllegalStateException();
    }

    public void calleeSinksThenThrows() {
        try {
            sinkThenThrow(source());
        } catch (IllegalStateException e) {
            counter++;
        }
    }

    public void sinkInLoopExitOnlyByThrow() {
        for (;;) {
            String s = source();
            sink(s);
            if (unknown()) {
                throw new IllegalStateException();
            }
        }
    }

    public void finallySink() {
        String s = "safe";
        try {
            s = source();
        } finally {
            sink(s);
        }
    }

    private void sinkStatic() {
        sink(staticValue);
    }

    public void sinkOnStaticInCallee() {
        staticValue = source();
        sinkStatic();
    }

    private Box getHeldBox(Holder h) {
        return h.box;
    }

    private void setHeldBox(Holder h, Box b) {
        h.box = b;
    }

    public void getterOfHeldBox() {
        Holder h = new Holder();
        h.box = new Box(source());
        sink(getHeldBox(h).f);
    }

    public void setterCreatesHeapLink() {
        Holder h = new Holder();
        Box b = new Box();
        b.f = source();
        setHeldBox(h, b);
        sink(h.box.f);
    }

    private void resetMiddle(Outer o) {
        o.middle = new Middle();
    }

    public void calleeReplacesIntermediateObject() {
        Outer o = new Outer();
        o.middle.box.f = source();
        resetMiddle(o);
        sink(o.middle.box.f);
    }

    public void intermediateReferenceSurvives() {
        Outer o = new Outer();
        o.middle.box.f = source();
        Middle m = o.middle;
        resetMiddle(o);
        sink(m.box.f);
    }

    static class Ref<T> {
        T value;
    }

    public void genericFieldWithCast() {
        Ref<Box> r = new Ref<>();
        r.value = wrap(source());
        sink(r.value.f);
    }

    public void objectTypedLocalCast() {
        Object o = wrap(source());
        Box b = (Box) o;
        sink(b.f);
    }

    public void listOfBoxesField() {
        List<Box> boxes = new ArrayList<>();
        boxes.add(wrap(source()));
        sink(boxes.get(0).f);
    }

    private String choose(String a, String b) {
        return unknown() ? a : b;
    }

    public void chooseEitherArgument() {
        sink(choose("safe", source()));
    }

    private String even(String x, int n) {
        return n <= 0 ? x : odd(x, n - 1);
    }

    private String odd(String x, int n) {
        return n <= 0 ? "safe" : even(x, n - 1);
    }

    public void mutualRecursion() {
        sink(even(source(), 4));
    }

    static class E {
        String f;
    }

    static class D {
        E e = new E();
    }

    static class C {
        D d = new D();
    }

    static class B {
        C c = new C();
    }

    static class A {
        B b = new B();
    }

    private void writeDepth5(A a, String x) {
        a.b.c.d.e.f = x;
    }

    private String readDepth5(A a) {
        return a.b.c.d.e.f;
    }

    public void depth5AcrossMethods() {
        A a = new A();
        writeDepth5(a, source());
        sink(readDepth5(a));
    }

    public void sameFieldNameOtherClass() {
        E e = new E();
        Box b = new Box();
        e.f = source();
        sink(b.f);
    }

    static class SubBox extends Box {
        String extra;
    }

    public void subclassFieldViaSuperType() {
        SubBox s = new SubBox();
        s.f = source();
        Box b = s;
        sink(b.f);
    }

    static class ShadowBox extends Box {
        String f;
    }

    public void shadowedFieldNotConfused() {
        ShadowBox s = new ShadowBox();
        s.f = source();
        Box b = s;
        sink(b.f);
    }

    static class DerivedBox extends Box {
        DerivedBox(String x) {
            super(x);
        }
    }

    public void superConstructorStoresField() {
        DerivedBox b = new DerivedBox(source());
        sink(b.f);
    }

    private Box fillAndReturnFresh(Box b, String x) {
        b.f = x;
        return new Box();
    }

    public void argumentMutatedButVariableReplaced() {
        Box b = new Box();
        Box old = b;
        b = fillAndReturnFresh(b, source());
        sink(old.f);
    }

    public void argumentMutatedResultRead() {
        Box b = new Box();
        b = fillAndReturnFresh(b, source());
        sink(b.f);
    }

    public void arrayCopy() {
        String[] a = new String[1];
        String[] b = new String[1];
        a[0] = source();
        System.arraycopy(a, 0, b, 0, 1);
        sink(b[0]);
    }

    public void entryParameterOnly(String param) {
        sink(param);
    }

    public void builderReadThenReset() {
        StringBuilder sb = new StringBuilder();
        sb.append(source());
        String t = sb.toString();
        sb.setLength(0);
        sink(t);
    }

    public void stringFormatVarargs() {
        sink(String.format("%s", source()));
    }

    public void iteratorLoopSink() {
        List<String> items = new ArrayList<>();
        items.add(source());
        for (String item : items) {
            sink(item);
        }
    }

    class InnerReader {
        void read() {
            sink(data);
        }
    }

    public void innerClassReadsOuterField() {
        this.data = source();
        new InnerReader().read();
    }

    public void requireNonNullKeepsFields() {
        Box b = new Box();
        b.f = source();
        Box c = java.util.Objects.requireNonNull(b);
        sink(c.f);
    }

    public void unmodelledLibraryCallKeepsArgument() {
        List<String> items = new ArrayList<>();
        items.add(source());
        java.util.Collections.shuffle(items);
        sink(items.get(0));
    }

    public void methodReferenceSink() {
        java.util.function.Consumer<String> c = this::sink;
        c.accept(source());
    }

    private Supplier<String> makeSupplier() {
        return () -> source();
    }

    public void lambdaCreatedInCallee() {
        sink(makeSupplier().get());
    }

    private Supplier<String> supplier;

    public void lambdaStoredInField() {
        this.supplier = () -> source();
        sink(this.supplier.get());
    }

    private String applyFn(Function<String, String> fn, String x) {
        return fn.apply(x);
    }

    public void helperWithTwoLambdas() {
        String a = applyFn(x -> x, "safe");
        sink(applyFn(x -> "safe", source()));
    }

    public void helperWithTwoLambdasTainting() {
        String a = applyFn(x -> "safe", "safe");
        sink(applyFn(x -> x, source()));
    }

    public void catchUsesTryLocal() {
        String s = "safe";
        try {
            s = source();
            Integer.parseInt(s);
        } catch (NumberFormatException e) {
            sink(s);
        }
    }

    private void sinkThenMaybeSpin(String x) {
        sink(x);
        while (true) {
            counter++;
            if (counter == 100) {
                return;
            }
        }
    }

    public void calleeWithRareExit() {
        sinkThenMaybeSpin(source());
    }
}

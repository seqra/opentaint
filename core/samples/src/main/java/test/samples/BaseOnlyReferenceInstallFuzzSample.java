package test.samples;

public class BaseOnlyReferenceInstallFuzzSample {
    private static String source() { return "tainted"; }
    private static void sink(String value) { }

    private static String stringAlias(String value) { return value; }
    private static Cell cellAlias(Cell value) { return value; }

    private static Cell makeCell(String value) { return new Cell(value); }
    private static Cell makeTaggedCell(String value, Tag tag) { return new Cell(value, tag); }
    private static Cell makeTaggedCell(Tag tag, String value) { return new Cell(tag, value); }
    private static Cell makeCellViaAlias(String value) { return new Cell(stringAlias(value)); }
    private static Cell makeCellNested(String value) { return makeCell(value); }

    private static void install(Cell cell, String value) { cell.set(value); }
    private static void installTagged(Cell cell, Tag tag, String value) { cell.setTagged(tag, value); }
    private static void installTagged(Cell cell, String value, Tag tag) { cell.setTagged(value, tag); }
    private static void installNested(Cell cell, String value) { install(cell, value); }
    private static Cell installAndReturn(Cell cell, String value) { cell.set(value); return cell; }

    public static void directConstructorInstall() {
        Cell cell = new Cell(source());
        sink(cell.value);
    }

    public static void constructorInstallFromLocal() {
        String value = source();
        Cell cell = new Cell(value);
        sink(cell.value);
    }

    public static void constructorInstallFromAlias() {
        String value = source();
        String alias = value;
        Cell cell = new Cell(alias);
        sink(cell.value);
    }

    public static void constructorInstallFromTwoAliases() {
        String value = source();
        String first = value;
        String second = first;
        Cell cell = new Cell(second);
        sink(cell.value);
    }

    public static void constructorInstallFromIdentity() {
        Cell cell = new Cell(stringAlias(source()));
        sink(cell.value);
    }

    public static void constructorInstallFromReferenceCast() {
        Object value = source();
        Cell cell = new Cell((String) value);
        sink(cell.value);
    }

    public static void constructorInstallFirstArgument() {
        Cell cell = new Cell(source(), new Tag());
        sink(cell.value);
    }

    public static void constructorInstallSecondArgument() {
        Cell cell = new Cell(new Tag(), source());
        sink(cell.value);
    }

    public static void directFactoryInstall() {
        Cell cell = makeCell(source());
        sink(cell.value);
    }

    public static void factoryInstallFromAlias() {
        String value = source();
        String alias = value;
        Cell cell = makeCell(alias);
        sink(cell.value);
    }

    public static void factoryInstallFromCast() {
        Object value = source();
        Cell cell = makeCell((String) value);
        sink(cell.value);
    }

    public static void nestedFactoryInstall() {
        Cell cell = makeCellNested(source());
        sink(cell.value);
    }

    public static void factoryAliasInsideInstall() {
        Cell cell = makeCellViaAlias(source());
        sink(cell.value);
    }

    public static void factoryInstallFirstArgument() {
        Cell cell = makeTaggedCell(source(), new Tag());
        sink(cell.value);
    }

    public static void factoryInstallSecondArgument() {
        Cell cell = makeTaggedCell(new Tag(), source());
        sink(cell.value);
    }

    public static void directSetterInstall() {
        Cell cell = new Cell();
        cell.set(source());
        sink(cell.value);
    }

    public static void setterInstallFromAlias() {
        String value = source();
        String alias = value;
        Cell cell = new Cell();
        cell.set(alias);
        sink(cell.value);
    }

    public static void setterInstallFromCast() {
        Object value = source();
        Cell cell = new Cell();
        cell.set((String) value);
        sink(cell.value);
    }

    public static void setterInstallThroughReceiverAlias() {
        Cell cell = new Cell();
        Cell alias = cell;
        alias.set(source());
        sink(cell.value);
    }

    public static void setterInstallThroughReceiverIdentity() {
        Cell cell = new Cell();
        cellAlias(cell).set(source());
        sink(cell.value);
    }

    public static void helperSetterInstall() {
        Cell cell = new Cell();
        install(cell, source());
        sink(cell.value);
    }

    public static void nestedHelperSetterInstall() {
        Cell cell = new Cell();
        installNested(cell, source());
        sink(cell.value);
    }

    public static void helperSetterInstallLastArgument() {
        Cell cell = new Cell();
        installTagged(cell, new Tag(), source());
        sink(cell.value);
    }

    public static void helperSetterInstallMiddleArgument() {
        Cell cell = new Cell();
        installTagged(cell, source(), new Tag());
        sink(cell.value);
    }

    public static void helperReturnsInstalledWrapper() {
        Cell cell = installAndReturn(new Cell(), source());
        sink(cell.value);
    }

    public static void constructorInstallThroughEnvelope() {
        Envelope envelope = new Envelope(new Cell(source()));
        sink(envelope.cell.value);
    }

    public static void constructorInstallThroughTwoEnvelopes() {
        OuterEnvelope outer = new OuterEnvelope(new Envelope(new Cell(source())));
        sink(outer.envelope.cell.value);
    }

    public static void setterInstallThroughEnvelope() {
        Envelope envelope = new Envelope(new Cell());
        envelope.cell.set(source());
        sink(envelope.cell.value);
    }

    public static void branchConstructorInstall() {
        String value = source();
        Cell cell;
        if (value != null) {
            cell = new Cell(value);
        } else {
            cell = new Cell();
        }
        sink(cell.value);
    }

    public static void branchSetterInstall() {
        String value = source();
        Cell cell = new Cell();
        if (value != null) {
            cell.set(value);
        }
        sink(cell.value);
    }

    private static final class Tag { }

    private static final class Cell {
        private String value;
        private Tag tag;

        Cell() { }
        Cell(String value) { this.value = value; }
        Cell(String value, Tag tag) { this.value = value; this.tag = tag; }
        Cell(Tag tag, String value) { this.tag = tag; this.value = value; }

        void set(String value) { this.value = value; }
        void setTagged(Tag tag, String value) { this.tag = tag; this.value = value; }
        void setTagged(String value, Tag tag) { this.value = value; this.tag = tag; }
    }

    private static final class Envelope {
        private final Cell cell;
        Envelope(Cell cell) { this.cell = cell; }
    }

    private static final class OuterEnvelope {
        private final Envelope envelope;
        OuterEnvelope(Envelope envelope) { this.envelope = envelope; }
    }
}

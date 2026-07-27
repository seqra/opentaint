package test.samples;

public class BaseOnlySummaryFieldExplosionSample {
    private static String source() {
        return "tainted";
    }

    private static void sink(String value) {
    }

    public static void fieldEnumerationExplosion(int readSelector, int writeSelector) {
        Fields fields = new Fields();
        String tainted = source();
        fields.f00 = tainted;
        fields.f01 = tainted;
        fields.f02 = tainted;
        fields.f03 = tainted;
        fields.f04 = tainted;
        fields.f05 = tainted;
        fields.f06 = tainted;
        fields.f07 = tainted;
        fields.f08 = tainted;
        fields.f09 = tainted;
        fields.f10 = tainted;
        fields.f11 = tainted;
        fields.f12 = tainted;
        fields.f13 = tainted;
        fields.f14 = tainted;
        fields.f15 = tainted;
        fields.f16 = tainted;
        fields.f17 = tainted;
        fields.f18 = tainted;
        fields.f19 = tainted;

        Fields result = permuteField(fields, readSelector, writeSelector);
        sink(result.f00);
    }

    private static Fields permuteField(Fields fields, int readSelector, int writeSelector) {
        String selected;
        switch (readSelector) {
            case 0: selected = fields.f00; break;
            case 1: selected = fields.f01; break;
            case 2: selected = fields.f02; break;
            case 3: selected = fields.f03; break;
            case 4: selected = fields.f04; break;
            case 5: selected = fields.f05; break;
            case 6: selected = fields.f06; break;
            case 7: selected = fields.f07; break;
            case 8: selected = fields.f08; break;
            case 9: selected = fields.f09; break;
            case 10: selected = fields.f10; break;
            case 11: selected = fields.f11; break;
            case 12: selected = fields.f12; break;
            case 13: selected = fields.f13; break;
            case 14: selected = fields.f14; break;
            case 15: selected = fields.f15; break;
            case 16: selected = fields.f16; break;
            case 17: selected = fields.f17; break;
            case 18: selected = fields.f18; break;
            default: selected = fields.f19;
        }

        switch (writeSelector) {
            case 0: fields.f00 = selected; break;
            case 1: fields.f01 = selected; break;
            case 2: fields.f02 = selected; break;
            case 3: fields.f03 = selected; break;
            case 4: fields.f04 = selected; break;
            case 5: fields.f05 = selected; break;
            case 6: fields.f06 = selected; break;
            case 7: fields.f07 = selected; break;
            case 8: fields.f08 = selected; break;
            case 9: fields.f09 = selected; break;
            case 10: fields.f10 = selected; break;
            case 11: fields.f11 = selected; break;
            case 12: fields.f12 = selected; break;
            case 13: fields.f13 = selected; break;
            case 14: fields.f14 = selected; break;
            case 15: fields.f15 = selected; break;
            case 16: fields.f16 = selected; break;
            case 17: fields.f17 = selected; break;
            case 18: fields.f18 = selected; break;
            default: fields.f19 = selected;
        }

        return fields;
    }

    private static class Fields {
        String f00;
        String f01;
        String f02;
        String f03;
        String f04;
        String f05;
        String f06;
        String f07;
        String f08;
        String f09;
        String f10;
        String f11;
        String f12;
        String f13;
        String f14;
        String f15;
        String f16;
        String f17;
        String f18;
        String f19;
    }
}

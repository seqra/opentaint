package test.samples;

public class BaseOnlySummaryFieldExplosionSample {
    private static String source() {
        return "tainted";
    }

    private static void sink(String value) {
    }

    public static void fieldEnumerationExplosion(int readSelector, int writeSelector) {
        Fields input = new Fields();
        String tainted = source();
        input.f00 = tainted;
        input.f01 = tainted;
        input.f02 = tainted;
        input.f03 = tainted;
        input.f04 = tainted;
        input.f05 = tainted;
        input.f06 = tainted;
        input.f07 = tainted;
        input.f08 = tainted;
        input.f09 = tainted;
        input.f10 = tainted;
        input.f11 = tainted;
        input.f12 = tainted;
        input.f13 = tainted;
        input.f14 = tainted;
        input.f15 = tainted;
        input.f16 = tainted;
        input.f17 = tainted;
        input.f18 = tainted;
        input.f19 = tainted;

        Fields result = permuteField(input, readSelector, writeSelector);
        sink(result.f00);
    }

    public static void exactFinalConvergence(int readSelector) {
        Fields input = new Fields();
        String tainted = source();
        input.f00 = tainted;
        input.f01 = tainted;

        sink(input.f00);
        convergeFieldPremises(input, readSelector);
    }

    public static void irrelevantCallConclusionSharing(int readSelector) {
        Fields input = new Fields();
        String tainted = source();
        input.f00 = tainted;
        input.f01 = tainted;

        String selected = convergeFieldPremisesAcrossIrrelevantCall(input, readSelector);
        sink(selected);
    }

    private static String convergeFieldPremisesAcrossIrrelevantCall(Fields input, int readSelector) {
        String selected;
        switch (readSelector) {
            case 0: selected = input.f00; break;
            default: selected = input.f01;
        }
        passthrough(selected);
        irrelevantCall();
        return selected;
    }

    private static void irrelevantCall() {
    }

    private static Fields permuteField(
            Fields input,
            int readSelector,
            int writeSelector) {
        String selected;
        switch (readSelector) {
            case 0: selected = input.f00; break;
            case 1: selected = input.f01; break;
            case 2: selected = input.f02; break;
            case 3: selected = input.f03; break;
            case 4: selected = input.f04; break;
            case 5: selected = input.f05; break;
            case 6: selected = input.f06; break;
            case 7: selected = input.f07; break;
            case 8: selected = input.f08; break;
            case 9: selected = input.f09; break;
            case 10: selected = input.f10; break;
            case 11: selected = input.f11; break;
            case 12: selected = input.f12; break;
            case 13: selected = input.f13; break;
            case 14: selected = input.f14; break;
            case 15: selected = input.f15; break;
            case 16: selected = input.f16; break;
            case 17: selected = input.f17; break;
            case 18: selected = input.f18; break;
            default: selected = input.f19;
        }

        switch (writeSelector) {
            case 0: input.f00 = selected; break;
            case 1: input.f01 = selected; break;
            case 2: input.f02 = selected; break;
            case 3: input.f03 = selected; break;
            case 4: input.f04 = selected; break;
            case 5: input.f05 = selected; break;
            case 6: input.f06 = selected; break;
            case 7: input.f07 = selected; break;
            case 8: input.f08 = selected; break;
            case 9: input.f09 = selected; break;
            case 10: input.f10 = selected; break;
            case 11: input.f11 = selected; break;
            case 12: input.f12 = selected; break;
            case 13: input.f13 = selected; break;
            case 14: input.f14 = selected; break;
            case 15: input.f15 = selected; break;
            case 16: input.f16 = selected; break;
            case 17: input.f17 = selected; break;
            case 18: input.f18 = selected; break;
            default: input.f19 = selected;
        }
        return input;
    }

    private static void convergeFieldPremises(Fields input, int readSelector) {
        String selected;
        switch (readSelector) {
            case 0: selected = input.f00; break;
            default: selected = input.f01;
        }
        passthrough(selected);
    }

    private static String passthrough(String value) {
        return value;
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

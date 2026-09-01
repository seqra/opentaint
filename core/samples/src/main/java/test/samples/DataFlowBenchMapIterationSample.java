package test.samples;

import java.util.HashMap;
import java.util.Map;

public class DataFlowBenchMapIterationSample {

    public void mapIterationIntFlow() {
        Map<String, Integer> tainted = new HashMap<>();
        tainted.put("entry", intSource());
        for (Map.Entry<String, Integer> entry : tainted.entrySet()) {
            intSink(entry.getValue());
        }
    }

    public void mapIterationStringFlow() {
        Map<String, String> tainted = new HashMap<>();
        tainted.put("entry", source());
        for (Map.Entry<String, String> entry : tainted.entrySet()) {
            sink(entry.getValue());
        }
    }

    public int intSource() { return 1; }

    public void intSink(int data) { }

    public String source() { return "tainted"; }

    public void sink(String data) { }
}

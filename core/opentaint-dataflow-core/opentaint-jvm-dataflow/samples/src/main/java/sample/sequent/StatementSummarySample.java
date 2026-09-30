package sample.sequent;

public class StatementSummarySample {
    static Object sField;
    Object f;
    StatementSummarySample next;

    Object fieldRead(StatementSummarySample y) { return y.f; }
    void fieldWrite(StatementSummarySample y, Object x) { y.f = x; }
    Object staticRead() { return sField; }
    void staticWrite(Object x) { sField = x; }
    Object arrayRead(Object[] y) { return y[0]; }
    void arrayWrite(Object[] y, Object x) { y[0] = x; }
    void selfWrite(StatementSummarySample a) { a.f = a; }
    String cast(Object y) { return (String) y; }
    int binary(int a, int b) { return a + b; }
    Object constant() { return "c"; }

    StatementSummarySample selfRead(StatementSummarySample start) {
        StatementSummarySample n = start;
        while (n.next != null) {
            n = n.next;
        }
        return n;
    }
}

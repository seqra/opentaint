package test.samples;

public class BaseOnlyTraceShapeFuzzSample {
    private static Token source() { return new Token(); }
    private static void sink(Response value) { }

    private static Response response(Token value) {
        Response response = new Response();
        response.body = value;
        return response;
    }

    private static Response probe(Response value) { return value; }
    private static Response relay(Response value) { return value; }
    private static Response project(Outer value) { return value.response; }

    private static Outer probedFactory(Token value) {
        Outer outer = new Outer();
        outer.response = probe(response(value));
        return outer;
    }

    private static Outer probedConstructorFactory(Token value) {
        return new Outer(probe(response(value)));
    }

    private static Outer doubleProbedFactory(Token value) {
        Outer outer = new Outer();
        outer.response = probe(probe(response(value)));
        return outer;
    }

    private static Outer relayedProbeFactory(Token value) {
        Outer outer = new Outer();
        outer.response = relay(probe(response(value)));
        return outer;
    }

    public static void projectedProbedFactory() {
        sink(project(probedFactory(source())));
    }

    public static void projectedProbedConstructorFactory() {
        sink(project(probedConstructorFactory(source())));
    }

    public static void projectedDoubleProbedFactory() {
        sink(project(doubleProbedFactory(source())));
    }

    public static void projectedRelayedProbeFactory() {
        sink(project(relayedProbeFactory(source())));
    }

    private static final class Token { }

    private static final class Response {
        Token body;
    }

    private static final class Outer {
        Response response;

        Outer() { }
        Outer(Response response) { this.response = response; }
    }
}

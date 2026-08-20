package test.samples;

import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.RestController;

@RestController
public final class ThreadStaticFieldSample {
    @GetMapping
    public void exportViaThread(String surveyId) {
        Holder.savePath = surveyId;
        new Thread(new AnswerTask()).start();
    }

    @GetMapping
    public void exportViaDirectCall(String surveyId) {
        Holder.savePath = surveyId;
        new ExcelWorker().run();
    }

    @GetMapping
    public void exportViaThreadSubclass(String surveyId) {
        Holder.savePath = surveyId;
        new ExcelWorker().start();
    }

    @GetMapping
    public void exportViaInterface(String surveyId) {
        Holder.savePath = surveyId;
        Runnable task = pick();
        task.run();
    }

    @GetMapping
    public void exportViaHelper(String surveyId) {
        Holder.savePath = surveyId;
        runIt(pick());
    }

    @GetMapping
    public void exportInstanceViaThreadSubclass(String surveyId) {
        ExcelWorker worker = new ExcelWorker();
        worker.instancePath = surveyId;
        worker.start();
    }

    @GetMapping
    public void exportInstanceViaDirectCall(String surveyId) {
        ExcelWorker worker = new ExcelWorker();
        worker.instancePath = surveyId;
        worker.run();
    }

    @GetMapping
    public void exportViaThreadSubclassNoStatic(String surveyId) {
        Holder.savePath = surveyId;
        new PlainWorker().start();
    }

    private static Runnable pick() {
        if (System.currentTimeMillis() > 0) {
            return new AnswerTask();
        }
        return new ExcelWorker();
    }

    private static void runIt(Runnable task) {
        task.run();
    }

    public static void sink(String path) {
        System.out.println(path);
    }

    public static final class Holder {
        public static String savePath;
    }

    public static final class AnswerTask implements Runnable {
        @Override
        public void run() {
            System.out.println("unrelated");
        }
    }

    public static class ExcelWorker extends Thread {
        public String instancePath;

        @Override
        public void run() {
            ThreadStaticFieldSample.sink(Holder.savePath);
            ThreadStaticFieldSample.sink(this.instancePath);
        }
    }

    public static final class PlainWorker extends Thread {
        @Override
        public void run() {
            ThreadStaticFieldSample.sink(Holder.savePath);
        }
    }
}

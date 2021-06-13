package info.kgeorgiy.ja.yaroshevskij.hello;

import info.kgeorgiy.java.advanced.hello.HelloServer;

import java.nio.charset.StandardCharsets;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.getIntegerArgument;

abstract public class AbstractUDPServer implements HelloServer {

    static final String USAGE = "Usage: HelloUDPServer port threads";
    static final int TERMINATION_TIMEOUT_SEC = 60;
    static final int RESPONSE_TIMEOUT_MILLIS = 500;

    protected static byte[] constructMessageBuffer(String message) {
        return ("Hello, " + message).getBytes(StandardCharsets.UTF_8);
    }

    protected void mainImpl(String[] args) {
        try {
            int port = getIntegerArgument(args, 0, "port");
            int threads = getIntegerArgument(args, 1, "threads");
            start(port, threads);
        } catch (IllegalArgumentException e) {
            System.err.println(USAGE);
            System.err.println(e.getMessage());
        }
    }

    protected static void shutdownService(ExecutorService service) {
        service.shutdown();
        try {
            if (!service.awaitTermination(TERMINATION_TIMEOUT_SEC, TimeUnit.SECONDS)) {
                service.shutdownNow();
            }
        } catch (InterruptedException e) {
            // ignored
        }
    }
}

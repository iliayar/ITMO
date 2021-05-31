package info.kgeorgiy.ja.yaroshevskij.hello;

import info.kgeorgiy.java.advanced.hello.HelloClient;

import java.nio.charset.StandardCharsets;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.TimeUnit;

import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.getArgument;
import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.getIntegerArgument;

abstract public class AbstractUDPClient implements HelloClient {

    static final String USAGE = "Usage: HelloUDPClient address port prefix threads requestsPerThread";
    static final int RESPONSE_TIMEOUT_MILLIS = 200;

    protected static String constructMessage(String prefix, int threadId, int order) {
        return prefix + threadId + "_" + order;
    }

    protected static byte[] constructMessageBuffer(String prefix, int threadId, int order) {
        return constructMessage(prefix, threadId, order).getBytes(StandardCharsets.UTF_8);
    }

    protected static void awaitEndless(ExecutorService service) throws InterruptedException {
        service.awaitTermination(Long.MAX_VALUE, TimeUnit.DAYS);
    }

    protected void mainImpl(String[] args) {
        try {
            String address = getArgument(args, 0, "address");
            int port = getIntegerArgument(args, 1, "port");
            String prefix = getArgument(args, 2, "prefix");
            int threads = getIntegerArgument(args, 3, "threads");
            int requestsPerThread = getIntegerArgument(args, 4, "requestsPerThread");
            run(address, port, prefix, threads, requestsPerThread);
        } catch (IllegalArgumentException e) {
            System.err.println(USAGE);
            System.err.println(e.getMessage());
        }
    }
}

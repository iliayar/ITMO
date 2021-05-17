package info.kgeorgiy.ja.yaroshevskij.hello;

import info.kgeorgiy.java.advanced.hello.HelloClient;

import java.io.IOException;
import java.net.*;
import java.nio.charset.StandardCharsets;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class HelloUDPClient implements HelloClient {

    static final String USAGE = "Usage: HelloUDPClient address port prefix threads requestsPerThread";
    static final int TIMEOUT_PER_REQUEST_SEC = 10;
    static final int RESPONSE_TIMEOUT_MILLIS = 200;

    public static void main(String[] args) {
        if (args == null || args.length != 5) {
            System.err.println(USAGE);
            return;
        }
        for (int i = 0; i < 5; ++i) {
            if (args[i] == null) {
                System.err.println(USAGE);
                return;
            }
        }

        try {
            String address = args[0];
            int port = Integer.parseInt(args[1]);
            String prefix = args[2];
            int threads = Integer.parseInt(args[3]);
            int requestsPerThread = Integer.parseInt(args[4]);
            new HelloUDPClient().run(address, port, prefix, threads, requestsPerThread);
        } catch (NumberFormatException e) {
            System.err.println(USAGE);
            System.err.println(e.getMessage());
        }
    }

    @Override
    public void run(String address, int port, String prefix, int threads, int requestsPerThread) {
        try {
            new Sender(address, port, prefix, requestsPerThread).execute(threads);
        } catch (UnknownHostException e) {
            throw new IllegalArgumentException("Invalid host provided: " + e.getMessage());
        } catch (InterruptedException e) {
            System.err.println("Interrupted, global timeout exceed");
        }
    }

    private static class Sender {

        private final InetAddress address;
        private final int port;
        private final String prefix;
        private final int requestsPerThread;

        public Sender(String address, int port, String prefix, int requestsPerThread) throws UnknownHostException {
            this.address = InetAddress.getByName(address);
            this.port = port;
            this.prefix = prefix;
            this.requestsPerThread = requestsPerThread;
        }

        public void execute(int threads) throws InterruptedException {
            final ExecutorService pool = Executors.newFixedThreadPool(threads);
            for (int i = 0; i < threads; ++i) {
                final int id = i;
                pool.submit(() -> sendTask(id));
            }
            pool.shutdown();
            pool.awaitTermination(TIMEOUT_PER_REQUEST_SEC * requestsPerThread, TimeUnit.SECONDS);
        }

        private void sendTask(int threadId) {
            try (DatagramSocket socket = new DatagramSocket()) {
                socket.setSoTimeout(RESPONSE_TIMEOUT_MILLIS);
                int sent = 0;
                byte[] responseBuffer = new byte[socket.getReceiveBufferSize()];
                while (sent < requestsPerThread) {
                    String message = prefix + threadId + "_" + sent;
                    byte[] messageBuffer = message.getBytes(StandardCharsets.UTF_8);
                    DatagramPacket packet = new DatagramPacket(messageBuffer, messageBuffer.length, address, port);
                    try {
                        socket.send(packet);
                        packet.setData(responseBuffer);
                        socket.receive(packet);

                        String response = new String(responseBuffer, packet.getOffset(), packet.getLength(),
                                StandardCharsets.UTF_8);
                        if (response.contains(message)) {
                            System.out.println(message);
                            System.out.println(response);
                            sent += 1;
                        }
                    } catch (IOException e) {
                        // ignored, retrying
                    }
                }
            } catch (SocketException e) {
                System.err.println(e.getMessage());
            }
        }
    }
}

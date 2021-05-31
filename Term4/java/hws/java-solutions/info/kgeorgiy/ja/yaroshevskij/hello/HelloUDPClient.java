package info.kgeorgiy.ja.yaroshevskij.hello;

import java.io.IOException;
import java.net.*;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.*;

public class HelloUDPClient extends AbstractUDPClient {

    public static void main(String[] args) {
        new HelloUDPClient().mainImpl(args);
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
            awaitEndless(pool);
        }

        private void sendTask(int threadId) {
            try (DatagramSocket socket = new DatagramSocket()) {
                socket.setSoTimeout(RESPONSE_TIMEOUT_MILLIS);
                int sent = 0;
                byte[] responseBuffer = createReceiveBuffer(socket);
                while (sent < requestsPerThread) {
                    String message = constructMessage(prefix, threadId, sent);
                    DatagramPacket packet = createPacket(message, address, port);
                    try {
                        socket.send(packet);
                        packet.setData(responseBuffer);
                        socket.receive(packet);

                        String response = packetToString(packet);
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

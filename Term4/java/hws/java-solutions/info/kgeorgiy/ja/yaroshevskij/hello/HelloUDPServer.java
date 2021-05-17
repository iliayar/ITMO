package info.kgeorgiy.ja.yaroshevskij.hello;

import info.kgeorgiy.java.advanced.hello.HelloServer;

import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.SocketException;
import java.nio.charset.StandardCharsets;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

public class HelloUDPServer implements HelloServer {

    static final String USAGE = "Usage: HelloUDPServer port threads";
    static final int TERMINATION_TIMEOUT_SEC = 60;
    static final int RESPONSE_TIMEOUT_MILLIS = 500;

    final Queue<Listener> listeners = new ConcurrentLinkedQueue<>();

    public static void main(String[] args) {
        if (args == null || args.length != 2 || args[0] == null || args[1] == null) {
            System.err.println(USAGE);
            return;
        }

        try {
            int port = Integer.parseInt(args[0]);
            int threads = Integer.parseInt(args[1]);
            try (HelloServer server = new HelloUDPServer()) {
                server.start(port, threads);
            }
        } catch (NumberFormatException e) {
            System.err.println(USAGE);
            System.err.println(e.getMessage());
        }
    }

    @Override
    public void start(int port, int threads) {
        try {
            listeners.add(new Listener(port, threads));
        } catch (SocketException e) {
            System.err.println("Cannot open socket: " + e.getMessage());
        }
    }

    @Override
    public void close() {
        listeners.stream().parallel().forEach(Listener::close);
    }

    static class Listener {
        private final ExecutorService workers;
        private final DatagramSocket socket;

        Listener(int port, int threads) throws SocketException {
            this.socket = new DatagramSocket(port);
            socket.setSoTimeout(RESPONSE_TIMEOUT_MILLIS);
            this.workers = Executors.newFixedThreadPool(threads);
            for (int i = 0; i < threads; ++i) {
                this.workers.submit(this::listen);
            }
        }

        private void listen() {
            try {
                byte[] buffer = new byte[socket.getReceiveBufferSize()];
                while (!socket.isClosed()) {
                    DatagramPacket packet = new DatagramPacket(buffer, buffer.length);
                    socket.receive(packet);
                    String message = "Hello, " + new String(buffer, packet.getOffset(), packet.getLength(), StandardCharsets.UTF_8);
                    byte[] messageBuffer = message.getBytes();
                    packet.setData(messageBuffer);
                    socket.send(packet);
                }
            } catch (IOException e) {
                System.err.println("Error occurred: " + e.getMessage());
            }
        }

        private void close() {
            socket.close();
            workers.shutdown();
            try {
                if (!workers.awaitTermination(TERMINATION_TIMEOUT_SEC, TimeUnit.SECONDS)) {
                    workers.shutdownNow();
                }
            } catch (InterruptedException e) {
                // ignored
            }
        }
    }
}

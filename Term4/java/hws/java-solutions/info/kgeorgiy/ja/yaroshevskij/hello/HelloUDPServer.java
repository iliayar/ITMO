package info.kgeorgiy.ja.yaroshevskij.hello;

import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.SocketException;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.*;


public class HelloUDPServer extends AbstractUDPServer {

    final Queue<Listener> listeners = new ConcurrentLinkedQueue<>();

    public static void main(String[] args) {
        try (HelloUDPServer server = new HelloUDPServer()) {
            server.mainImpl(args);
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
                byte[] buffer = createReceiveBuffer(socket);
                while (!socket.isClosed()) {
                    DatagramPacket packet = createPacket(buffer);
                    socket.receive(packet);
                    byte[] messageBuffer = constructMessageBuffer(packetToString(packet));
                    packet.setData(messageBuffer);
                    socket.send(packet);
                }
            } catch (IOException e) {
                System.err.println("Error occurred: " + e.getMessage());
            }
        }

        private void close() {
            socket.close();
            shutdownService(workers);
        }
    }
}

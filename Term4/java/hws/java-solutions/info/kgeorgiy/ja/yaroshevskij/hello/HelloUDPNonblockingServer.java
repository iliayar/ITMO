package info.kgeorgiy.ja.yaroshevskij.hello;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.SocketAddress;
import java.nio.ByteBuffer;
import java.nio.channels.DatagramChannel;
import java.nio.channels.SelectionKey;
import java.nio.channels.Selector;
import java.util.ArrayDeque;
import java.util.Queue;
import java.util.concurrent.ConcurrentLinkedQueue;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.*;

public class HelloUDPNonblockingServer extends AbstractUDPServer {

    private final Queue<Receiver> receivers = new ArrayDeque<>();

    public static void main(String[] args) {
        try (HelloUDPNonblockingServer server = new HelloUDPNonblockingServer()) {
            server.mainImpl(args);
        }
    }

    @Override
    public void start(int port, int threads) {
        try {
            receivers.add(new Receiver(port, threads));
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

    @Override
    public void close() {
        receivers.forEach(Receiver::close);
    }

    static class Receiver {

        private final Queue<MessageData> messages;
        private final Selector selector;
        private final DatagramChannel channel;
        private final ExecutorService executor;
        private final ExecutorService converters;

        Receiver(int port, int threads) throws IOException {
            this.messages = new ConcurrentLinkedQueue<>();
            this.converters = Executors.newFixedThreadPool(threads);
            this.selector = Selector.open();
            this.channel = createChannel();
            SocketAddress address = new InetSocketAddress(port);
            channel.bind(address);
            channel.register(selector, SelectionKey.OP_READ);
            executor = Executors.newSingleThreadExecutor();
            executor.submit(this::listen);
        }

        private void convert(ByteBuffer buffer, SocketAddress address, SelectionKey key) {
                String request = byteBufferToString(buffer);
                messages.add(new MessageData(request, address));
                key.interestOpsOr(SelectionKey.OP_WRITE);
        }

        private void listen() {
            while (!Thread.interrupted() && selector.isOpen()) {
                try {
                    selector.select(this::handle);
                } catch (IOException e) {
                    e.printStackTrace();
                }
            }
        }

        private void handle(SelectionKey key) {
            if (key.isReadable()) {
                receive(key);
            } else if (key.isWritable()) {
                send();
            }
            if (messages.isEmpty()) {
                key.interestOps(SelectionKey.OP_READ);
            }
        }

        private void receive(SelectionKey key) {
            ByteBuffer buffer = ByteBuffer.allocate(NONBLOCKING_BUFFER_SIZE);
            try {
                SocketAddress address = channel.receive(buffer);
                converters.submit(() -> convert(buffer, address, key));
            } catch (IOException e) {
                System.err.println("Failed to receive data: " + e.getMessage());
            }
        }

        private void send() {
            MessageData messageData = messages.poll();
            if (messageData != null) {
                try {
                    channel.send(ByteBuffer.wrap(messageData.message), messageData.address);
                } catch (IOException e) {
                    System.err.println("Failed to send data: " + e.getMessage());
                }
            }
        }

        public void close() {
            try {
                channel.close();
                selector.close();
            } catch (IOException e) {
                System.err.println("Failed to close receiver: " + e.getMessage());
            }
            shutdownService(executor);
        }

        static class MessageData {
            byte[] message;
            SocketAddress address;

            MessageData(String message, SocketAddress address) {
                this.message = constructMessageBuffer(message);
                this.address = address;
            }
        }

    }
}

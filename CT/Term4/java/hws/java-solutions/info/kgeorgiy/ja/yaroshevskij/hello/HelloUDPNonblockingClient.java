package info.kgeorgiy.ja.yaroshevskij.hello;

import java.io.IOException;
import java.net.InetSocketAddress;
import java.net.UnknownHostException;
import java.nio.ByteBuffer;
import java.nio.channels.DatagramChannel;
import java.nio.channels.SelectionKey;
import java.nio.channels.Selector;

import static info.kgeorgiy.ja.yaroshevskij.hello.Utils.*;

public class HelloUDPNonblockingClient extends AbstractUDPClient {

    public static void main(String[] args) {
        new HelloUDPNonblockingClient().mainImpl(args);
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

    static class Sender {
        private final InetSocketAddress address;
        private final String prefix;
        private final int requestsPerThread;

        public Sender(String address, int port, String prefix, int requestsPerThread) throws UnknownHostException {
            this.address = new InetSocketAddress(address, port);
            this.prefix = prefix;
            this.requestsPerThread = requestsPerThread;
        }

        public void execute(int threads) throws InterruptedException {
            Selector selector;
            try {
                selector = Selector.open();
                for (int i = 0; i < threads; i++) {
                    DatagramChannel channel = createChannel();
                    channel.register(selector, SelectionKey.OP_WRITE, new ClientContext(i));
                }
            } catch (IOException e) {
                return;
            }
            send(selector);
        }

        private void send(Selector selector) {
            while (!Thread.interrupted() && !selector.keys().isEmpty()) {
                try {
                    if (selector.select(this::handler, HelloUDPClient.RESPONSE_TIMEOUT_MILLIS) == 0) {
                        selector.keys().stream()
                                .filter(SelectionKey::isWritable)
                                .forEach(this::handler);
                    }
                } catch (IOException e) {
                    // ignored
                }
            }
        }

        private void handler(SelectionKey key) {
            DatagramChannel channel = (DatagramChannel) key.channel();
            ClientContext context = (ClientContext) key.attachment();
            if (key.isWritable()) {
                if (context.send(channel)) {
                    key.interestOps(SelectionKey.OP_READ);
                }
            } else if (key.isReadable()) {
                if (context.receive(channel)) {
                    key.interestOps(SelectionKey.OP_WRITE);
                }
            }
        }

        class ClientContext {
            int threadId;
            int sent;

            ClientContext(int threadId) {
                this.threadId = threadId;
                this.sent = 0;
            }

            public boolean send(DatagramChannel channel) {
                byte[] message = constructMessageBuffer(prefix, threadId, sent);
                try {
                    channel.send(ByteBuffer.wrap(message), address);
                } catch (IOException e) {
                    System.err.println("Error during sending: " + e.getMessage());
                    return false;
                }
                return true;
            }

            public boolean receive(DatagramChannel channel) {
                ByteBuffer buffer = ByteBuffer.allocate(NONBLOCKING_BUFFER_SIZE);
                try {
                    channel.receive(buffer);
                    String response = byteBufferToString(buffer);
                    String message = constructMessage(prefix, threadId, sent);
                    if (response.contains(message)) {
                        System.out.println(message);
                        System.out.println(response);
                        sent += 1;
                        if (sent == requestsPerThread) {
                            channel.close();
                            return false;
                        }
                    }
                } catch (IOException e) {
                    System.err.println("Error during receiving: " + e.getMessage());
                    return false;
                }
                return true;
            }
        }
    }

}

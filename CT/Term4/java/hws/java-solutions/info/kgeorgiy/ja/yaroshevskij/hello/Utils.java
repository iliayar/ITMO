package info.kgeorgiy.ja.yaroshevskij.hello;

import java.io.IOException;
import java.net.DatagramPacket;
import java.net.DatagramSocket;
import java.net.InetAddress;
import java.net.SocketException;
import java.nio.ByteBuffer;
import java.nio.channels.DatagramChannel;
import java.nio.charset.StandardCharsets;

public class Utils {

    public static final int NONBLOCKING_BUFFER_SIZE = 512;

    public static DatagramPacket createPacket(byte[] buffer, InetAddress address, int port) {
        return new DatagramPacket(buffer, buffer.length, address, port);
    }

    public static DatagramPacket createPacket(String message, InetAddress address, int port) {
        return createPacket(message.getBytes(StandardCharsets.UTF_8), address, port);
    }

    public static DatagramPacket createPacket(byte[] buffer) {
        return new DatagramPacket(buffer, buffer.length);
    }

    public static byte[] createReceiveBuffer(DatagramSocket socket) throws SocketException {
        return new byte[socket.getReceiveBufferSize()];
    }

    public static String packetToString(DatagramPacket packet) {
        return bufferToString(packet.getData(), packet.getOffset(), packet.getLength());

    }

    public static String byteBufferToString(ByteBuffer buffer) {
        return bufferToString(buffer.array(), 0, buffer.position());
    }

    private static String bufferToString(byte[] buffer, int offset, int length) {
        return new String(buffer, offset, length, StandardCharsets.UTF_8);
    }

    private static void checkArgument(String[] args, int id, String name) {
        if (args == null || args.length <= id || args[id] == null) {
            throw new IllegalArgumentException("Argument " + name + " was not provided");
        }
    }

    public static int getIntegerArgument(String[] args, int id, String name) {
        checkArgument(args, id, name);
        try {
            return Integer.parseInt(args[id]);
        } catch (NumberFormatException e) {
            throw new IllegalArgumentException("Argument " + name + " is not a number");
        }
    }

    public static String getArgument(String[] args, int id, String name) {
        checkArgument(args, id, name);
        return args[id];
    }

    public static DatagramChannel createChannel() throws IOException {
        DatagramChannel channel = DatagramChannel.open();
        channel.configureBlocking(false);
        return channel;
    }
}

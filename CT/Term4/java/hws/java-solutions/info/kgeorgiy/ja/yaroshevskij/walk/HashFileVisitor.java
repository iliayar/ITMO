package info.kgeorgiy.ja.yaroshevskij.walk;

import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStream;
import java.nio.file.FileVisitResult;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.SimpleFileVisitor;
import java.nio.file.attribute.BasicFileAttributes;

class HashFileVisitor extends SimpleFileVisitor<Path> {

    private final BufferedWriter output;
    private static final int BUFFER_SIZE = 512;

    HashFileVisitor(BufferedWriter output) {
        this.output = output;
    }

    @Override
    public FileVisitResult visitFile(Path file, BasicFileAttributes attrs) throws IOException {
        this.output.write(hashToString(calcuateHash(file)) + " " + file.toString());
        this.output.newLine();
        return FileVisitResult.CONTINUE;
    }

    @Override
    public FileVisitResult visitFileFailed(Path file, IOException e) throws IOException {
        this.output.write(hashToString(0) + " " + file.toString());
        this.output.newLine();
        RecursiveWalk.error("Failed to calculate hash of " + file, e);
        return FileVisitResult.CONTINUE;
    }

    public static String hashToString(long h) {
        return String.format("%016x", h);
    }

    private long calcuateHash(Path file) {
        try (InputStream inp = Files.newInputStream(file);) {
            byte[] buffer = new byte[BUFFER_SIZE];
            int length = 0;
            long h = 0;
            while ((length = inp.read(buffer)) >= 0) {
                for (int i = 0; i < length; i++) {
                    h = (h << 8) | Byte.toUnsignedLong(buffer[i]);
                    long high = h & (0xFFL << 56);
                    if (high != 0) {
                        h ^= high >> 48;
                    }
                    h &= ~high;
                }
            }
            return h;
        } catch (IOException e) {
            RecursiveWalk.error("Error ocured while calculating hash", e);
        } catch (SecurityException e) {
            RecursiveWalk.securityError("reading file " + file.toString(), e);
        }
        return 0;
    }

}

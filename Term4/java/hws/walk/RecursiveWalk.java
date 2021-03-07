package info.kgeorgiy.ja.yaroshevskij.walk;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.FileAlreadyExistsException;
import java.nio.file.Files;
import java.nio.file.InvalidPathException;
import java.nio.file.Path;
import java.nio.file.Paths;

public class RecursiveWalk {

    public static void main(String[] args) {
        if (args == null) {
            error("null arguments provided");
            return;
        }
        if (args.length != 2) {
            error("Expect 2 arguments: <input file> <output file>, provided " + args.length + " arguments");
            return;
        }
        if (args[0] == null || args[1] == null) {
            error("Provided arguments are null");
            return;
        }

        try {
            Path inputPath = Paths.get(args[0]);
            try {
                Path outputPath = Paths.get(args[1]);

                try {
                    Path outputDirPath = outputPath.getParent();
                    if (outputDirPath != null) {
                        Files.createDirectories(outputDirPath);
                    }
                } catch (FileAlreadyExistsException e) {
                    error("File at output file path already exists", e);
                } catch (IOException e) {
                    error("Cannot create output file path", e);
                } catch (SecurityException e) {
                    securityError("creating path to output file", e);
                }

                try {
                    if (Files.isSameFile(inputPath, outputPath)) {
                        error("Input and output files are same");
                        return;
                    }
                } catch (IOException | SecurityException e) {
                }

                recursiveWalk(inputPath, outputPath);

            } catch (InvalidPathException e) {
                error("Output file path is invalid", e);
            } catch (SecurityException e) {
                securityError("reading output file path", e);
            }
        } catch (InvalidPathException e) {
            error("Input file path is invalid", e);
        } catch (SecurityException e) {
            securityError("reading input file path", e);
        }
    }

    private static void recursiveWalk(Path inputPath, Path outputPath) {

        try (BufferedReader input = Files.newBufferedReader(inputPath)) {
            try (BufferedWriter output = Files.newBufferedWriter(outputPath)) {

                try {
                    String line;
                    while ((line = input.readLine()) != null) {
                        try {
                            Files.walkFileTree(Paths.get(line), new HashFileVisitor(output));
                        } catch (IOException e) {
                            error("Failed to write to output line " + line, e);
                        } catch (InvalidPathException e) {
                            output.write(HashFileVisitor.hashToString(0) + " " + line);
                            output.newLine();
                            error("Provided path " + line + " is invalid", e);
                        }
                    }
                } catch (IOException e) {
                    error("Error while processing input file", e);
                }

            } catch (IOException e) {
                error("Failed to open output file", e);
            } catch (SecurityException e) {
                securityError("writing output file", e);
            }
        } catch (FileNotFoundException e) {
            error("Input file does not exists", e);
        } catch (IOException e) {
            error("Failed to open input file", e);
        } catch (SecurityException e) {
            securityError("reading input file", e);
        }
    }

    public static void error(String msg) {
        System.err.println(msg);
    }

    public static void error(String msg, Exception e) {
        System.err.println(msg + ": " + e.getMessage());
    }

    public static void securityError(String msg, SecurityException e) {
        error("Security error ocured during " + msg + ": " + e.getMessage(), e);
    }

}

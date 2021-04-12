package info.kgeorgiy.ja.yaroshevskij.implementor;

import info.kgeorgiy.java.advanced.implementor.ImplerException;

import java.io.BufferedWriter;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Helper class for {@link Implementor} to handle writing to resulting {@code .java} file.
 */
public class ClassWriter {

    /**
     * Indentation string
     */
    private final static String INDENT = "    ";

    /**
     * {@link BufferedWriter} for resulting {@code .java} file
     */
    private final BufferedWriter out;

    /**
     * New class name. Identical to origin class name with {@code Impl} suffix
     */
    private final String className;
    /**
     * Class package name. Identical to origin class package
     */
    private final String packageName;
    /**
     * Current indent level
     */
    private int indentLevel = 0;

    /**
     * Constructor from origin class and path to folder, in which its new implementation class will be written
     *
     * @param aClass The origin class to implement
     * @param path   The folder to write implementation in
     * @throws IOException If failed writing to destination folder or to new {@code .jar} file
     */
    ClassWriter(Class<?> aClass, Path path) throws IOException {
        if (aClass.getPackage() == null) {
            packageName = "";
        } else {
            packageName = aClass.getPackage().getName();
        }

        Path implementationPath = path.resolve(getPackageSeparated(File.separator));
        Files.createDirectories(implementationPath);

        className = aClass.getSimpleName() + "Impl";

        out = Files.newBufferedWriter(implementationPath.resolve(className + ".java"));
    }

    /**
     * Getter for {@link #className}
     *
     * @return New class name
     */
    public String getClassName() {
        return className;
    }

    /**
     * Getter for {@link #packageName}, but also replace dots with provided string.
     *
     * @param separator The string to replace dots with
     * @return String identical to package name but with dots replaced with {@code separator}
     */
    public String getPackageSeparated(String separator) {
        return packageName.replace(".", separator);
    }

    /**
     * Writes {@link System#lineSeparator()} to file
     *
     * @throws IOException If failed to write
     */
    public void newLine() throws IOException {
        write(System.lineSeparator());
    }

    /**
     * Write string to file. Escapes non ASCII characters with hex value prefixed with {@code \\u}
     * Writes chars to {@link #out}.
     * @param s      String to write
     * @throws IOException     If failed to write
     */
    public void write(String s) throws IOException {
        out.write(s.chars().mapToObj(c -> {
            if (c > 255) {
                return String.format("\\u%04x", c);
            } else {
                return String.valueOf((char) c);
            }
        }).collect(Collectors.joining()));
    }


    /**
     * Write indentation corresponding to current indent level
     *
     * @throws IOException If failed to write
     * @see #indentLevel
     */
    public void indent() throws IOException {
        write(INDENT.repeat(indentLevel));
    }

    /**
     * Write string to file with current indentation and new line in the end
     *
     * @param s String to write
     * @throws IOException If failed to write
     */
    public void writeLine(String s) throws IOException {
        indent();
        write(s);
        newLine();
    }

    /**
     * Write open curly bracket without indent, new line and increase indent
     *
     * @throws IOException If failed to write
     * @see #indent()
     */
    public void blockBegin() throws IOException {
        write(" {");
        newLine();
        indentLevel += 1;
    }

    /**
     * Write close curly bracket with indent, followed by new line. Decrease indent
     *
     * @throws IOException If failed to write
     * @see #write(String)
     * @see #indent()
     */
    public void blockEnd() throws IOException {
        indent();
        write("}");
        newLine();
        indentLevel -= 1;
    }

    /**
     * Writes an array elements using provided function, writes the separator between each to calls
     *
     * @param elements  Array of elements to write
     * @param writer    The function which writes one element
     * @param separator Separating string
     * @param <T>       Type of elements to write, using provided function
     * @throws IOException If failed to write
     * @see ImplerConsumer
     */
    public <T> void joinWithBy(T[] elements, ImplerConsumer<T> writer, String separator) throws IOException {
        joinWithBy(Arrays.asList(elements), writer, separator);
    }

    /**
     * Writes elements separated by commas. Shorthand for {@link #joinWithBy(Object[], ImplerConsumer, String)} with
     * commas as separator
     *
     * @param elements Elements to write
     * @param writer   The function which writes one element
     * @param <T>      The of elements to write, using provided function
     * @throws IOException If failed to write
     * @see #joinWithBy(Object[], ImplerConsumer, String)
     * @see ImplerConsumer
     */
    public <T> void joinWith(T[] elements, ImplerConsumer<T> writer) throws IOException {
        joinWithBy(elements, writer, ", ");
    }

    /**
     * Short hand for {@link #joinWithBy(Iterable, ImplerConsumer, String)} with comma as separator
     *
     * @param elements Array of elements to write
     * @param writer   The function which writes one element
     * @param <T>      Type of elements to write, using provided function
     * @param <I>      Iterable class type
     * @throws IOException If failed to write
     */
    public <T, I extends Iterable<T>> void joinWith(I elements, ImplerConsumer<T> writer) throws IOException {
        joinWithBy(elements, writer, ", ");
    }

    /**
     * Writes elements separated, the variant of {@link #joinWithBy(Object[], ImplerConsumer, String)} for
     * {@link Iterable} types
     *
     * @param elements  Array of elements to write
     * @param writer    The function which writes one element
     * @param separator Separating string
     * @param <T>       Type of elements to write, using provided function
     * @param <I>       Iterable class type
     * @throws IOException If failed to write
     * @see ImplerConsumer
     */
    public <T, I extends Iterable<T>> void joinWithBy(I elements, ImplerConsumer<T> writer, String separator) throws
            IOException {
        int i = 0;
        for (T element : elements) {
            if (i != 0) {
                write(separator);
            }
            writer.accept(element);
            i++;
        }
    }

    /**
     * Close the resulting {@code .jar} file
     *
     * @throws IOException If failed to close file
     */
    public void close() throws IOException {
        out.close();
    }

    /**
     * Consumer interface which can throw a {@link IOException}
     *
     * @param <T> Accepted type
     */
    @FunctionalInterface
    interface ImplerConsumer<T> {
        /**
         * Call function with parameter
         *
         * @param t Argument to function
         * @throws IOException If function throws
         */
        void accept(T t) throws IOException;
    }
}

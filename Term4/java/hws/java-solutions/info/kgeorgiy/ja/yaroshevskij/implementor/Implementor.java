package info.kgeorgiy.ja.yaroshevskij.implementor;

import info.kgeorgiy.java.advanced.implementor.ImplerException;
import info.kgeorgiy.java.advanced.implementor.JarImpler;

import javax.tools.JavaCompiler;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Parameter;
import java.net.URISyntaxException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Predicate;
import java.util.jar.Attributes;
import java.util.jar.JarEntry;
import java.util.jar.JarOutputStream;
import java.util.jar.Manifest;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Implementation of {@link JarImpler} with ability to call from command line.
 *
 * @see Implementor#main(String[])
 * @see Implementor#implement(Class, Path)
 */
public class Implementor implements JarImpler {

    /**
     * Map to convert modifier integer value to appropriate string.
     * The key is predicate from {@link java.lang.Integer} fetched from {@link Method#getModifiers()},
     * {@link Class#getModifiers()} or {@link Constructor#getModifiers()} to {@link String}, which represent this
     * modifier.
     */
    private final static Map<Predicate<Integer>, String> modifiers = Map.of(
            Modifier::isProtected, "protected",
            Modifier::isPublic, "public"
    );

    /**
     * Map to check class if {@link Implementor#implement(Class, Path)} can generate implementation for.
     */
    private final static Map<Predicate<Class<?>>, String> unimplementableClasses = Map.of(
            c -> Modifier.isPrivate(c.getModifiers()), "private class",
            c -> Modifier.isFinal(c.getModifiers()), "final class",
            c -> c.equals(Enum.class), "enum",
            Class::isPrimitive, "primitive",
            Class::isArray, "array"
    );

    /**
     * {@link ClassWriter}, which handles write operations.
     */
    private ClassWriter writer;

    /**
     * Running {@link Implementor} from command line. Two call options available
     * <p>
     * {@code <program> -jar <Class name> <Jar file>}
     * <p>
     * {@code <program> <Class name> <Implementation path>}
     * <p>
     * The first one create the implementation for {@code Class} and writes it to specified {@code Jar file}
     * The second also implements provided {@code Class}, but writes source code to {@code Implementation path}
     * {@code Class name} is the full name of class to implement. {@code Implementation path} is folder, to which
     * generated {@code .java} file will be written.
     *
     * @param args command line arguments.
     */
    public static void main(String[] args) {
        if (args != null && args.length >= 2 && args[0] != null && args[1] != null) {
            if (args.length == 3 && "-jar".equals(args[0]) && args[2] != null) {
                Path jarFile = Path.of(args[2]);
                try {
                    Class<?> aClass = Class.forName(args[1]);
                    new Implementor().implementJar(aClass, jarFile);
                } catch (ClassNotFoundException e) {
                    System.err.println("Cannot find class " + args[1]);
                } catch (ImplerException e) {
                    System.err.println("Cannot implement " + args[1] + ": " + e.getMessage());
                }
                return;
            } else if (args.length == 2) {
                Path path = Path.of(args[1]);
                try {
                    Class<?> aClass = Class.forName(args[0]);
                    new Implementor().implement(aClass, path);
                } catch (ClassNotFoundException e) {
                    System.err.println("Cannot find class " + args[0]);
                } catch (ImplerException e) {
                    System.err.println("Cannot implement " + args[0] + ": " + e.getMessage());
                }
                return;
            }
        }
        System.err.println("Usage: <program> -jar <Class name> <Jar file>");
        System.err.println("       <program> <Class name> <Implementation path>");
    }

    /**
     * Generates implementation for {@code aClass} and writes it in the folder {@code path}. The abstract methods in
     * generated class are
     * implemented and return the default values: {@code 0} for any primitive number type, {@code false} for boolean,
     * and {@code null} for all other types.
     *
     * @param aClass Class to generate implementation for
     * @param path   Folder, in which generated class will be written
     * @throws ImplerException If cannot generate implementation for provided class or cannot write class to file
     */
    @Override
    public void implement(Class<?> aClass, Path path) throws ImplerException {
        if (aClass == null) {
            throw new ImplerException("Provided class in null");
        }
        if (path == null) {
            throw new ImplerException("Provided path is null");
        }

        for (Map.Entry<Predicate<Class<?>>, String> entry : unimplementableClasses.entrySet()) {
            if (entry.getKey().test(aClass)) {
                throw new ImplerException("Cannot implement " + entry.getValue());
            }
        }
        try {
            writer = new ClassWriter(aClass, path);
            writeFile(aClass);
        } catch (IOException e) {
            throw new ImplerException("Failed to write to file: " + e.getMessage());
        } finally {
            try {
                writer.close();
            } catch (IOException e) {
                throw new ImplerException("Failed to close file: " + e.getMessage());
            }
        }
    }

    /**
     * Recursively deletes temporary directory.
     *
     * @param path Path to be deleted
     * @throws ImplerException If cannot delete provided {@code path}
     */
    private void cleanup(Path path) throws ImplerException {
        try {
            Files.walk(path)
                    .sorted(Comparator.reverseOrder())
                    .map(Path::toFile)
                    .forEach(File::delete);
        } catch (IOException e) {
            throw new ImplerException("Cannot cleanup temp directory");
        }
    }

    /**
     * Generate implementation for class, compiles it, and writes to {@code .jar} file
     *
     * @param aClass class to generate implementation for
     * @param path   resulting jar file, in which implementation will e written
     * @throws ImplerException If cannot generate implementation for provided class or cannot write class to file
     * @see #implement(Class, Path)
     */
    @Override
    public void implementJar(Class<?> aClass, Path path) throws ImplerException {
        Path temp;
        try {
            temp = Files.createTempDirectory(Path.of("."), "Implementer-");
        } catch (IOException | SecurityException e) {
            throw new ImplerException("Cannot create temporary file");
        }
        try {
            implement(aClass, temp);

            Path classpath;
            try {
                classpath =
                        Path.of(aClass.getProtectionDomain().getCodeSource().getLocation().toURI());
            } catch (NullPointerException | URISyntaxException e) {
                System.err.println("Cannot fetch classpath from provided class");
                classpath = Path.of(".");
            }

            compile(classpath.toAbsolutePath(), temp);

            createJar(path, temp);
        } finally {
            cleanup(temp);
        }
    }

    /**
     * Compile class located in {@code temp/<package>/<classname>Iml.java}.
     *
     * @param classpath Classpath of class to compile
     * @param temp   The directory in which class sources are located
     * @throws ImplerException If failed to compile class
     */
    private void compile(Path classpath, Path temp) throws ImplerException {
        JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
        if (compiler == null) {
            throw new ImplerException("Cannot find java compiler");
        }
        String[] args =
                Stream.of(temp.resolve(writer.getPackageSeparated(File.separator))
                                .resolve(writer.getClassName() + ".java").toString(),
                        "-cp", classpath.toString()).toArray(String[]::new);
        int exitCode = compiler.run(null, null, null, args);
        if (exitCode != 0) {
            throw new ImplerException("Could not compile implemented class");
        }
    }

    /**
     * Create jar archive from compiled class, which locates in {@code temp/<package>/<classname>Iml.class} and saves
     * it to {@code path} folder
     *
     * @param path   The output directory for jar archive
     * @param temp   The directory in which compiled class is located
     * @throws ImplerException If failed to write jar archive
     */
    private void createJar(Path path, Path temp) throws ImplerException {
        Manifest manifest = new Manifest();
        Attributes attributes = manifest.getMainAttributes();
        attributes.put(Attributes.Name.MANIFEST_VERSION, "1.0");

        try (JarOutputStream output = new JarOutputStream(Files.newOutputStream(path), manifest)) {
            output.putNextEntry(new JarEntry(
                    writer.getPackageSeparated("/") + "/" + writer.getClassName() + ".class"));
            Files.copy(
                    temp.resolve(writer.getPackageSeparated(File.separator))
                            .resolve(writer.getClassName() + ".class"), output);
            output.closeEntry();
        } catch (IOException e) {
            throw new ImplerException("Cannot open jar file: " + e.getMessage());
        }
    }

    /**
     * Generate code of {@code package} in which class located and the code of whole class.
     *
     * @param aClass class to write to {@link #writer}
     * @throws ImplerException If class has only private constructors
     * @throws IOException If filed to write
     * @see #implement(Class, Path)
     * @see #writeClass(Class)
     * @see #writePackage(Package)
     */
    private void writeFile(Class<?> aClass) throws IOException, ImplerException {
        writePackage(aClass.getPackage());
        writeClass(aClass);
    }

    /**
     * Generate code for whole class
     *
     * @param aClass class to generate code for
     * @throws IOException If failed to write
     * @throws ImplerException If class has no public or protected constructors
     * @see #implement(Class, Path)
     * @see #writeClassSignature(Class)
     * @see #writeConstructor(Constructor)
     * @see #writeMethods(Class)
     */
    private void writeClass(Class<?> aClass) throws IOException, ImplerException {
        writer.indent();
        writeClassSignature(aClass);
        writer.blockBegin();
        writeConstructors(aClass.getDeclaredConstructors());
        writeMethods(aClass);
        writer.blockEnd();
    }

    /**
     * Generates code for class signature: name, implemented interfaces ot extending classes. Name is Origin class
     * name with {@code Impl} suffix.
     *
     * @param aClass class to generate signature for
     * @throws IOException if cannot implement or write class
     */
    private void writeClassSignature(Class<?> aClass) throws IOException {
        writer.write("class " + writer.getClassName());
        if (aClass.isInterface()) {
            writer.write(" implements ");
        } else {
            writer.write(" extends ");
        }
        writeType(aClass);
    }

    /**
     * Generate code for class constructors. Also check if class has public constructors
     *
     * @param constructors constructors to generate code for
     * @throws ImplerException If class has no public constructors
     * @throws IOException If wailed to write
     * @see #writeConstructor(Constructor)
     */
    private void writeConstructors(Constructor<?>[] constructors) throws IOException, ImplerException {
        List<Constructor<?>> nonPrivateConstructors = Arrays.stream(constructors)
                .filter(ctr -> !Modifier.isPrivate(ctr.getModifiers()))
                .collect(Collectors.toList());
        if (constructors.length > 0 && nonPrivateConstructors.size() == 0) {
            throw new ImplerException("Cannot implement class without public or protected constructors");
        }
        for (Constructor<?> constructor : nonPrivateConstructors) {
            writeConstructor(constructor);
        }
    }

    /**
     * Generate code for class constructor: signature and body, in which calls @{code super()}. The result if valid
     * constructor for new class
     *
     * @param constructor Constructor to generate code for
     * @throws IOException If failed to write
     * @see #writeModifiers(int)
     * @see #writeExceptions(Class[])
     * @see #writeParameter(Parameter)
     */
    private void writeConstructor(Constructor<?> constructor) throws IOException {
        writer.indent();
        writeModifiers(constructor.getModifiers());
        writer.write(writer.getClassName() + "(");
        writeParameters(constructor.getParameters());
        writer.write(")");
        writeExceptions(constructor.getExceptionTypes());
        writer.blockBegin();
        writer.indent();
        writer.write("super(");
        writer.joinWith(constructor.getParameters(), (p) -> writer.write(p.getName()));
        writer.write(");");
        writer.newLine();
        writer.blockEnd();
    }

    /**
     * Generate code for class methods. Only implements abstract methods.
     *
     * @param aClass Class to fetch methods from
     * @throws IOException If Cannot write to file
     * @see #writeMethod(Method)
     */
    private void writeMethods(Class<?> aClass) throws IOException {
        List<Method> methods = collectMethods(aClass).stream()
                .map(MethodWrapper::getMethod)
                .filter(m -> Modifier.isAbstract(m.getModifiers()))
                .collect(Collectors.toList());
        for (Method method : methods) {
            writeMethod(method);
        }
    }

    /**
     * Generate code for single method: signature and method body.
     *
     * @param method Method to generate code for
     * @throws IOException If failed to write
     * @see #writeMethodSignature(Method)
     * @see #writeMethodBody(Method)
     */
    private void writeMethod(Method method) throws IOException {
        writer.indent();
        writeMethodSignature(method);
        writer.blockBegin();
        writeMethodBody(method);
        writer.blockEnd();
    }

    /**
     * Recursively reads method from class, its superclasses and interfaces. Do not add methods, which are identical
     * by signature and parameters using {@link MethodWrapper}
     *
     * @param aClass The class to collect methods from
     * @return {@link Set} of unique methods.
     * @see MethodWrapper
     */
    private Set<MethodWrapper> collectMethods(Class<?> aClass) {
        Set<MethodWrapper> methods = new HashSet<>();
        Queue<Class<?>> queue = new ArrayDeque<>();
        queue.add(aClass);
        while (!queue.isEmpty()) {
            Class<?> clazz = queue.remove();
            methods.addAll(
                    Arrays.stream(clazz.getDeclaredMethods())
                            .map(MethodWrapper::new)
                            .collect(Collectors.toList()));
            if (clazz.getSuperclass() != null) {
                queue.add(clazz.getSuperclass());
            }
            queue.addAll(Arrays.asList(clazz.getInterfaces()));
        }
        return methods;
    }

    /**
     * Generate method signature: return type, name, parameters, thrown exceptions. Its all are identical to origin
     * class
     *
     * @param method Method to generate signature for
     * @throws IOException If failed to write
     * @see #writeModifiers(int)
     * @see #writeType(Class)
     * @see #writeParameter(Parameter)
     * @see #writeExceptions(Class[])
     */
    private void writeMethodSignature(Method method) throws IOException {
        writeModifiers(method.getModifiers());
        writeType(method.getReturnType());
        writer.write(" " + method.getName() + "(");
        writeParameters(method.getParameters());
        writer.write(")");
        writeExceptions(method.getExceptionTypes());
    }

    /**
     * Generate code for method body. Its empty if method returns nothing, and return default value otherwise.
     *
     * @param method Method to generate body for
     * @throws IOException If failed to write
     * @see #writeDefaultValue(Class)
     */
    private void writeMethodBody(Method method) throws IOException {
        if (!method.getReturnType().equals(Void.TYPE)) {
            writer.indent();
            writer.write("return ");
            writeDefaultValue(method.getReturnType());
            writer.write(";");
            writer.newLine();
        }
    }

    /**
     * Generate code for method signature throwing exceptions including {@code throws} word. Exceptions are identical
     * to origin method. Writes
     * nothing if list is empty.
     *
     * @param exceptions The list of exceptions
     * @throws IOException If failed to write
     */
    private void writeExceptions(Class<?>[] exceptions) throws IOException {
        if (exceptions.length != 0) {
            writer.write(" throws ");
            writer.joinWith(exceptions, this::writeType);
        }
    }

    /**
     * Write parameters list in method signature, separated by comma. For each parameter writes its type and name
     *
     * @param parameters Parameter to write
     * @throws IOException If failed to write
     * @see #writeParameter(Parameter)
     */
    private void writeParameters(Parameter[] parameters) throws IOException {
        writer.joinWith(parameters, this::writeParameter);
    }

    /**
     * Write class type fetched from {@link Class#getCanonicalName()}
     *
     * @param clazz Class, which type to write
     * @throws IOException If failed to write
     */
    private void writeType(Class<?> clazz) throws IOException {
        writer.write(clazz.getCanonicalName());
    }

    /**
     * Write modifiers for constructors, methods, and class.
     *
     * @param mod The value got from {@link Method#getModifiers()}, {@link Class#getModifiers()} or
     *            {@link Constructor#getModifiers()}
     * @throws IOException If failed to write
     */
    private void writeModifiers(int mod) throws IOException {
        for (Map.Entry<Predicate<Integer>, String> entry : modifiers.entrySet()) {
            if (entry.getKey().test(mod)) {
                writer.write(entry.getValue() + " ");
            }
        }
    }

    /**
     * Write single parameter in method signature. Write type and name separated by space.
     *
     * @param parameter Parameter to write
     * @throws IOException If failed to write
     */
    private void writeParameter(Parameter parameter) throws IOException {
        writeType(parameter.getType());
        writer.write(" " + parameter.getName());
    }

    /**
     * Write package of implemented class.
     *
     * @param pkg Package to write
     * @throws IOException If failed to write
     */
    private void writePackage(Package pkg) throws IOException {
        if (pkg != null) {
            writer.writeLine("package " + pkg.getName() + ";");
        }
    }

    /**
     * Write default value for provided class. Write {@code 0} for primitive number type, {@code false} for {@code
     * boolean} and {@code null} for all other types.
     *
     * @param clazz Type to write default value for
     * @throws IOException If failed to write
     */
    private void writeDefaultValue(Class<?> clazz) throws IOException {
        if (clazz.isPrimitive()) {
            if (clazz.equals(Boolean.TYPE)) {
                writer.write("false");
            } else {
                writer.write("0");
            }
        } else {
            writer.write("null");
        }
    }

    /**
     * Wrapper for {@link Method} for to not comparing methods classes, which one is declared in. Also implements
     * hash code, that do not depend on declared class.
     */
    static class MethodWrapper {
        /**
         * Hash base. Small prime number. Equals {@value #BASE}
         */
        private final static int BASE = 31;
        /**
         * Hash modulus. Big prime number. Equals {@value #MOD}
         */
        private final static int MOD = 133711;

        /**
         * Wrapping {@link Method} object
         */
        private final Method method;

        /**
         * Constructor from method, to wrap.
         *
         * @param method Method to wrap
         */
        MethodWrapper(Method method) {
            this.method = method;
        }

        /**
         * Getter for {@link #method}
         *
         * @return Wrapped method
         */
        Method getMethod() {
            return method;
        }

        /**
         * Check the methods equality, and not comparing classes, its declared in
         *
         * @param obj Another method to compare to
         * @return True if methods are equals by return type, parameters and name
         */
        @Override
        public boolean equals(Object obj) {
            if (obj == null) {
                return false;
            }
            if (!(obj instanceof MethodWrapper)) {
                return false;
            }
            Method other = ((MethodWrapper) obj).getMethod();
            if (!other.getName().equals(method.getName())) {
                return false;
            }
            if (!method.getReturnType().equals(other.getReturnType())) {
                return false;
            }
            Class<?>[] parameters = method.getParameterTypes();
            Class<?>[] parametersOther = other.getParameterTypes();
            if (parameters.length != parametersOther.length) {
                return false;
            }
            for (int i = 0; i < parameters.length; ++i) {
                if (!parameters[i].equals(parametersOther[i])) {
                    return false;
                }
            }
            return true;
        }

        /**
         * Hash of method, includes its return type, parameters and name
         *
         * @return Hash code of method, that do not depends on declared class
         */
        @Override
        public int hashCode() {
            int hash = method.getName().hashCode();
            hash = (hash * BASE + method.getReturnType().hashCode()) * BASE;
            for (Class<?> parameter : method.getParameterTypes()) {
                hash = (hash * BASE + parameter.hashCode()) % MOD;
            }
            return hash;
        }
    }
}

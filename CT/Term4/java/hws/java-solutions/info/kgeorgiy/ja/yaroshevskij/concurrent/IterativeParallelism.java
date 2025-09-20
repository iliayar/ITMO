package info.kgeorgiy.ja.yaroshevskij.concurrent;

import info.kgeorgiy.java.advanced.concurrent.ListIP;
import info.kgeorgiy.java.advanced.mapper.ParallelMapper;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class IterativeParallelism implements ListIP {

    private final ParallelMapper mapper;

    public IterativeParallelism(ParallelMapper mapper) {
        this.mapper = mapper;
    }
    public IterativeParallelism() {
        this.mapper = null;
    }

    @Override
    public String join(int threads, List<?> list) throws InterruptedException {
        return execute(threads, list, stream -> stream.map(Object::toString),
                stream -> stream.flatMap(Function.identity()).collect(Collectors.joining()));
    }

    @Override
    public <T> List<T> filter(int threads, List<? extends T> list, Predicate<? super T> predicate) throws InterruptedException {
        return execute(threads, list, stream -> stream.filter(predicate), this::streamOfStreamsToList);
    }

    @Override
    public <T, U> List<U> map(int threads, List<? extends T> list, Function<? super T, ? extends U> function) throws InterruptedException {
        return execute(threads, list, stream -> stream.map(function), this::streamOfStreamsToList);
    }

    @Override
    public <T> T maximum(int threads, List<? extends T> list, Comparator<? super T> comparator) throws InterruptedException {
        return execute(threads, list, stream -> stream.max(comparator).orElse(null));
    }

    @Override
    public <T> T minimum(int threads, List<? extends T> list, Comparator<? super T> comparator) throws InterruptedException {
        return execute(threads, list, stream -> stream.min(comparator).orElse(null));
    }

    @Override
    public <T> boolean all(int threads, List<? extends T> list, Predicate<? super T> predicate) throws InterruptedException {
        return execute(threads, list, stream -> stream.allMatch(predicate),
                stream -> stream.allMatch(Boolean::booleanValue));
    }

    @Override
    public <T> boolean any(int threads, List<? extends T> list, Predicate<? super T> predicate) throws InterruptedException {
        return execute(threads, list, stream -> stream.anyMatch(predicate),
                stream -> stream.anyMatch(Boolean::booleanValue));
    }

    private <T> List<Stream<? extends T>> splitList(int threadsNumber, List<? extends T> list) {
        if(threadsNumber <= 0) {
            throw new IllegalArgumentException("Thread count must be positive number");
        }
        if (list.size() == 0) {
            return List.of();
        }
        threadsNumber = Math.min(threadsNumber, list.size());
        int segmentSize = list.size() / threadsNumber;
        int extraSize = list.size() - segmentSize * threadsNumber;
        segmentSize += 1;
        List<Stream<? extends T>> result = new ArrayList<>();
        for (int i = 0; i < list.size(); i += segmentSize) {
            if (extraSize == 0) {
                segmentSize -= 1;
            }
            if (extraSize >= 0) {
                extraSize -= 1;
            }
            result.add(list.subList(i, i + segmentSize).stream());
        }
        return result;
    }

    private <T> List<T> streamOfStreamsToList(Stream<? extends Stream<? extends T>> stream) {
        return stream.flatMap(Function.identity()).collect(Collectors.toList());
    }

    private <T> T execute(int threads, List<? extends T> list, Function<Stream<? extends T>, T> function) throws InterruptedException {
        return execute(threads, list, function, function);
    }

    private <T, U, R> R execute(int threads, List<? extends T> list,
                                Function<Stream<? extends T>, U> function,
                                Function<Stream<? extends U>, R> resulting) throws InterruptedException {
        return executeStreams(splitList(threads, list), function, resulting);
    }

    private <T, U, R> R executeStreams(List<Stream<? extends T>> list, Function<Stream<? extends T>, U> function,
                                       Function<Stream<? extends U>, R> resulting) throws InterruptedException {
        if(this.mapper != null) {
            return resulting.apply(mapper.map(function, list).stream());
        }
        List<U> results = new ArrayList<>();
        List<Thread> threads = new ArrayList<>();
        for (int i = 0; i < list.size(); ++i) {
            results.add(null);
            threads.add(createThread(i, list.get(i), function, results));
        }
        executeThreads(threads);
        return resulting.apply((results.stream()));
    }

    private <T, R> Thread createThread(int i, Stream<? extends T> stream, Function<Stream<? extends T>, R> function,
                                       List<R> results) {
        return new Thread(() -> results.set(i, function.apply(stream)));
    }

    private void executeThreads(List<Thread> threads) throws InterruptedException {
        for (Thread thread : threads) {
            thread.start();
        }
        for (Thread thread : threads) {
            thread.join();
        }
    }
}

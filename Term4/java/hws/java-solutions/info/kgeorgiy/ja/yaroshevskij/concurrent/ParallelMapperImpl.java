package info.kgeorgiy.ja.yaroshevskij.concurrent;

import info.kgeorgiy.java.advanced.mapper.ParallelMapper;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;
import java.util.function.Function;
import java.util.Collections;

public class ParallelMapperImpl implements ParallelMapper {

    final private List<Thread> threads;
    final private Queue<Runnable> queue;

    public ParallelMapperImpl(int threadsNumber) {
        if (threadsNumber <= 0) {
            throw new IllegalArgumentException("Thread count must be positive number");
        }
        this.queue = new ArrayDeque<>();
        this.threads = new ArrayList<>();
        for (int i = 0; i < threadsNumber; ++i) {
            this.threads.add(new Thread(this::threadLoop));
            this.threads.get(i).start();
        }
    }

    private void threadLoop() {
        try {
            while (!Thread.interrupted()) {
                Runnable task;
                synchronized (queue) {
                    if (queue.isEmpty()) {
                        queue.wait();
                    }
                    task = queue.poll();
                }
                if (task != null) {
                    task.run();
                }
            }
        } catch (InterruptedException e) {
            // ignored
        }
    }

    @Override
    public <T, R> List<R> map(Function<? super T, ? extends R> function, List<? extends T> list) throws InterruptedException {
        TasksList<T, R> tasks = new TasksList<>(function, list);
        tasks.runTasks();
        return tasks.getResults();
    }

    @Override
    public void close() {
        threads.forEach(Thread::interrupt);
        for (Thread t : threads) {
            try {
                t.join();
            } catch (InterruptedException e) {
                // ignored
            }
        }
    }

    class TasksList<T, R> {
        private final List<? extends T> list;
        private final Function<? super T, ? extends R> function;
        private final List<R> results;
        volatile int tasksDoneCount;

        TasksList(Function<? super T, ? extends R> function, List<? extends T> list) {
            this.function = function;
            this.list = list;
            this.results = new ArrayList<>(Collections.nCopies(list.size(), null));
            this.tasksDoneCount = 0;
        }

        public void runTasks() {
            for (int i = 0; i < list.size(); ++i) {
                final int index = i;
                synchronized (queue) {
                    queue.add(() -> {
                        results.set(index, function.apply(list.get(index)));
                        taskDone();
                    });
                    queue.notify();
                }
            }
        }

        synchronized private void taskDone() {
            tasksDoneCount++;
            if (tasksDoneCount == list.size()) {
                notify();
            }
        }

        synchronized public List<R> getResults() throws InterruptedException {
            if (tasksDoneCount != list.size()) {
                wait();
            }
            return results;
        }
    }
}

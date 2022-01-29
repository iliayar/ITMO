package stack;

import org.openjdk.jmh.annotations.*;
import org.openjdk.jmh.infra.Blackhole;
import org.openjdk.jmh.runner.Runner;
import org.openjdk.jmh.runner.RunnerException;
import org.openjdk.jmh.runner.options.Options;
import org.openjdk.jmh.runner.options.OptionsBuilder;

import java.util.Random;
import java.util.concurrent.ThreadLocalRandom;
import java.util.concurrent.TimeUnit;

@OutputTimeUnit(TimeUnit.NANOSECONDS)
@Warmup(iterations = 5, time = 1, timeUnit = TimeUnit.SECONDS)
@Measurement(iterations = 10, time = 1, timeUnit = TimeUnit.SECONDS)
@BenchmarkMode(Mode.AverageTime)
@Fork(1)
@State(Scope.Benchmark)
public class StackBenchmark {
    @Param({"1", "10", "50", "100"})
    public int work = 0;

    private final Stack s = new StackImpl();

    @Group("stack")
    @Benchmark
    public void push() {
        Random r = ThreadLocalRandom.current();
        Blackhole.consumeCPU(r.nextInt(work));
        s.push(r.nextInt());
    }

    @Group("stack")
    @Benchmark
    public int pop() {
        Random r = ThreadLocalRandom.current();
        Blackhole.consumeCPU(r.nextInt(work));
        return s.pop();
    }


    public static void main(String[] args) throws RunnerException {
        Options opt = new OptionsBuilder()
                .include(StackBenchmark.class.getSimpleName())
                .forks(1)
                .threads(4) // CHANGE ME!
                .build();
        new Runner(opt).run();
    }
}

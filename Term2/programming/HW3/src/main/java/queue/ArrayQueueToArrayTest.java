package queue;

import java.net.MalformedURLException;
import java.util.Arrays;
import java.util.Deque;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public class ArrayQueueToArrayTest extends ArrayQueueTest<ArrayQueueToArrayTest.ToArrayQueue> {
    public ArrayQueueToArrayTest() {
        super(ToArrayQueue::new);
    }

    public static void main(final String[] args) {
        new ArrayQueueToArrayTest().test();
    }

    @Override
    protected void linearTest(final Deque<Object> expected, final ToArrayQueue actual) {
        assertEquals("toArray()", Arrays.asList(expected.toArray()), Arrays.asList(actual.toArray()));
    }

    static class ToArrayQueue extends ArrayQueueTest.Queue {
        private final ZMethod<Object[]> toArray;

        public ToArrayQueue(final String className, final Mode mode) throws MalformedURLException, NoSuchMethodException, ClassNotFoundException {
            super(className, mode);
            toArray = findMethod("toArray");
        }

        public Object[] toArray() { return toArray.invoke(); }
    }
}

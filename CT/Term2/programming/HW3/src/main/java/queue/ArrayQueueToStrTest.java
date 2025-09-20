package queue;

import java.net.MalformedURLException;
import java.util.Deque;

/**
 * @author Georgiy Korneev (kgeorgiy@kgeorgiy.info)
 */
public class ArrayQueueToStrTest extends ArrayQueueTest<ArrayQueueToStrTest.ToStrQueue> {
    public ArrayQueueToStrTest() {
        super(ToStrQueue::new);
    }

    public static void main(final String[] args) {
        new ArrayQueueToStrTest().test();
    }

    @Override
    protected void linearTest(final Deque<Object> expected, final ToStrQueue actual) {
        assertEquals("toStr()", expected.toString(), actual.toString());
    }

    static class ToStrQueue extends ArrayQueueTest.Queue {
        private final ZMethod<String> toStr;

        public ToStrQueue(final String className, final Mode mode) throws MalformedURLException, NoSuchMethodException, ClassNotFoundException {
            super(className, mode);
            toStr = findMethod("toStr");
        }

        @Override
        public String toString() {
            return toStr.invoke();
        }
    }
}

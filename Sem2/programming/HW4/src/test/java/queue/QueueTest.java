package queue;


import org.junit.Test;
import static org.junit.Assert.*;

import java.math.BigInteger;
import java.util.function.Function;
import java.util.function.Predicate;

public class QueueTest {


    @Test
    public void Test() {
        Queue q = new LinkedQueue();

        for(int i = 0; i < 10; ++i) {
            q.enqueue(Integer.valueOf(i));
        }
        assertEquals(10, q.size());
        assertEquals(false, q.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(Integer.valueOf(i), q.element());
            assertEquals(Integer.valueOf(i), q.dequeue());
        }
        assertEquals(true, q.isEmpty());
        for(int i = 0; i < 10; ++i) {
            q.enqueue(Integer.valueOf(i));
        }
        q.clear();
        assertEquals(true, q.isEmpty());

        q = new ArrayQueue();

        for(int i = 0; i < 10; ++i) {
            q.enqueue(Integer.valueOf(i));
        }
        assertEquals(10, q.size());
        assertEquals(false, q.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(Integer.valueOf(i), q.element());
            assertEquals(Integer.valueOf(i), q.dequeue());
        }
        assertEquals(true, q.isEmpty());
        for(int i = 0; i < 10; ++i) {
            q.enqueue(Integer.valueOf(i));
        }
        q.clear();
        assertEquals(true, q.isEmpty());
    }


    @Test
    public void TestPredicate() {
        Queue q;

        Queue q1 = new LinkedQueue();
        for(int i = 0; i < 10; ++i) {
            q1.enqueue(BigInteger.valueOf(i));
        }
        Predicate<Object> p = new Predicate<Object>() {
                @Override
                public boolean test(Object x) {
                    return ((BigInteger)x).compareTo(BigInteger.valueOf(5)) > 0;
                }
            };
        q = q1.filter(p);


        assertEquals(4, q.size());
        for (int i = 0; i < 6; ++i) {
            q1.dequeue();
        }
        for(int i = 6; i < 10; ++i) {
            q1.dequeue();
            assertEquals(BigInteger.valueOf(i), q.dequeue());
        }
    }


    @Test
    public void TestFunction() {
        Queue q;

        Queue q1 = new LinkedQueue();
        for (int i = 0; i < 10; ++i) {
            q1.enqueue(BigInteger.valueOf(i));
        }


        Function<Object, Object> func = new Function<Object, Object>() {
                @Override
                public Object apply(Object arg0) {
                    return ((BigInteger)arg0).multiply(BigInteger.valueOf(2));
                }
            };

        q = q1.map(func);

        assertEquals(10, q.size());
        for (int i = 0; i < 10; ++i) {
            assertEquals(BigInteger.valueOf(i).multiply(BigInteger.valueOf(2)), q.dequeue());
        }
    }
}

package queue;


import org.junit.Test;
import static org.junit.Assert.*;

public class QueueTest {

    @Test
    public void ModuleTest() {
        assertEquals(true, ArrayQueueModule.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(i,ArrayQueueModule.size());
            ArrayQueueModule.enqueue(Integer.valueOf(i));
        }
        ArrayQueueModule.clear();
        assertEquals(true, ArrayQueueModule.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(i,ArrayQueueModule.size());
            ArrayQueueModule.enqueue(Integer.valueOf(i));
        }
        assertEquals(false, ArrayQueueModule.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(10 - i, ArrayQueueModule.size());
            assertEquals(Integer.valueOf(i),ArrayQueueModule.element());
            assertEquals(Integer.valueOf(i),ArrayQueueModule.dequeue());
        }
        assertEquals(true, ArrayQueueModule.isEmpty());
    }
    @Test
    public void ADTTest() {
        ArrayQueueADT queue = new ArrayQueueADT();
        assertEquals(true, ArrayQueueADT.isEmpty(queue));
        for(int i = 0; i < 10; ++i) {
            assertEquals(i,ArrayQueueADT.size(queue));
            ArrayQueueADT.enqueue(queue, Integer.valueOf(i));
        }
        ArrayQueueADT.clear(queue);
        assertEquals(true, ArrayQueueADT.isEmpty(queue));
        for(int i = 0; i < 10; ++i) {
            assertEquals(i,ArrayQueueADT.size(queue));
            ArrayQueueADT.enqueue(queue, Integer.valueOf(i));
        }
        assertEquals(false, ArrayQueueADT.isEmpty(queue));
        for(int i = 0; i < 10; ++i) {
            assertEquals(10 - i, ArrayQueueADT.size(queue));
            assertEquals(Integer.valueOf(i),ArrayQueueADT.element(queue));
            assertEquals(Integer.valueOf(i),ArrayQueueADT.dequeue(queue));
        }
        assertEquals(true, ArrayQueueADT.isEmpty(queue));


        ArrayQueueADT q1 = new ArrayQueueADT();
        ArrayQueueADT q2 = new ArrayQueueADT();

        for(int i = 0; i < 10; ++i) {
            ArrayQueueADT.enqueue(q1, Integer.valueOf(i));
            ArrayQueueADT.enqueue(q2, Integer.valueOf(i));
        }
        for(int i = 0; i < 10; ++i) {
            assertEquals(Integer.valueOf(i), ArrayQueueADT.dequeue(q1));
            assertEquals(Integer.valueOf(i), ArrayQueueADT.dequeue(q2));
        }
    }
    @Test
    public void Test() {
        ArrayQueue queue = new ArrayQueue();
        assertEquals(true, queue.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(i,queue.size());
            queue.enqueue(Integer.valueOf(i));
        }
        queue.clear();
        assertEquals(true, queue.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(i,queue.size());
            queue.enqueue(Integer.valueOf(i));
        }
        assertEquals(false, queue.isEmpty());
        for(int i = 0; i < 10; ++i) {
            assertEquals(10 - i, queue.size());
            assertEquals(Integer.valueOf(i),queue.element());
            assertEquals(Integer.valueOf(i),queue.dequeue());
        }
        assertEquals(true, queue.isEmpty());


        ArrayQueue q1 = new ArrayQueue();
        ArrayQueue q2 = new ArrayQueue();

        for(int i = 0; i < 10; ++i) {
            q1.enqueue(Integer.valueOf(i));
            q2.enqueue(Integer.valueOf(i));
        }
        for(int i = 0; i < 10; ++i) {
            assertEquals(Integer.valueOf(i), q1.dequeue());
            assertEquals(Integer.valueOf(i), q2.dequeue());
        }
    }

    @Test
    public void TestDequeue() {
        ArrayQueueADT q = new ArrayQueueADT();
        ArrayQueueADT.enqueue(q, Integer.valueOf(1));
        ArrayQueueADT.enqueue(q, Integer.valueOf(2));
        ArrayQueueADT.push(q, Integer.valueOf(3));


        assertEquals(Integer.valueOf(3), ArrayQueueADT.element(q));
        assertEquals(Integer.valueOf(3), ArrayQueueADT.dequeue(q));
        assertEquals(Integer.valueOf(2), ArrayQueueADT.peek(q));
        assertEquals(Integer.valueOf(2), ArrayQueueADT.remove(q));
        assertEquals(Integer.valueOf(1), ArrayQueueADT.peek(q));
        assertEquals(Integer.valueOf(1), ArrayQueueADT.element(q));
        assertEquals(Integer.valueOf(1), ArrayQueueADT.dequeue(q));
    }

}

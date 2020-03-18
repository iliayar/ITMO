package queue;



// inv: queue = {q1(tail), q2, .. , qn(head)}
//      |queue| >= 0
//      tail != head
public class ArrayQueueModule {

    private static int tail = 0;
    private static int head = 0;

    private static int length = 0;

    private static Object[] array = new Object[2];

    // Pre:
    // Post: |queue'| = 2*|queue| if array.length == |queue| tail != head
    private static void expandArrayNeeded() {
        if (head == tail && length != 0) {
            Object[] temp = new Object[array.length * 2];
            System.arraycopy(array, head, temp, array.length + head, array.length - head);
            System.arraycopy(array, 0, temp, 0, tail);
            array = temp;
            head = array.length / 2 + head;
        }
    }

    // Pre: x != null queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {x(tail), q1, q2, .. , qn(head)}
    public static void enqueue(Object x) {
        array[tail] = x;
        tail = (tail+1) % array.length;
        expandArrayNeeded();
        length++;
        // printArray();
    }

    // Pre: x != null queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {q1(tail), q2, .., qn, x(head)}
    public static void push(Object x) {
        head = (head - 1 + array.length) % array.length;
        array[head] = x;
        expandArrayNeeded();
        length++;
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: q1
    public static Object peek() {
        if (length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return array[(tail - 1 + array.length) % array.length];
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: q1 queue' = {q2(tail), q3, .., qn(head)}
    public static Object remove() {
        if (length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        tail = (tail - 1 + array.length) % array.length;
        Object tmp =  array[tail];
        array[tail] = null;
        length--;
        return tmp;
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: qn queue' = {q1(tail), q2, .., q(n-1)(head)}
    public static Object dequeue() {
        if (length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        Object t = array[head];
        array[head] = null;
        head = (head + 1) % array.length;
        length--;
        // printArray();
        return t;
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: qn
    public static Object element() {
        if (length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return array[head];
    }

    // Pre:
    // Post |queue|
    public static int size() {
        return length;
    }

    // Pre:
    // Post: true if |queue| == 0 else false
    public static boolean isEmpty() {
        return length == 0;
    }

    // Pre:
    // Post: queue = {} |queue| = 0
    public static void clear() {
        array = new Object[2];
        length = 0;
        head = 0;
        tail = 0;
    }
}

package queue;



public class ArrayQueueModule {

    private static int tail = 0;
    private static int head = 0;

    private static int length = 0;

    private static Object[] array = new Object[2];

    private static void expandArrayNeeded() {
        if (head == tail && length != 0) {
            Object[] temp = new Object[array.length * 2];
            System.arraycopy(array, head, temp, array.length + head, array.length - head);
            System.arraycopy(array, 0, temp, 0, tail);
            array = temp;
            head = array.length / 2 + head;
        }
    }

    // Pre: x != null
    // Post: array[tail] = x and tail' = tail + 1 % array.size
    public static void enqueue(Object x) {
        array[tail] = x;
        tail = (tail+1) % array.length;
        expandArrayNeeded();
        length++;
        // printArray();
    }

    // Pre: x != null
    // Post: array[head'] = x and head' = head - 1 % array.size
    public static void push(Object x) {
        head = (head - 1 + array.length) % array.length;
        array[head] = x;
        expandArrayNeeded();
        length++;
    }

    // Pre: size > 0
    // Post: array[tail - 1 % array.size]
    public static Object peek() {
        if (length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return array[(tail - 1 + array.length) % array.length];
    }

    // Pre: size > 0
    // Post: array[tail] and tail' = tail - 1 % array.size
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

    // Pre: size > 0
    // Post: array[head] head' = head + 1 % array.size
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

    // Pre: size > 0
    // Post: array[head]
    public static Object element() {
        if (length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return array[head];
    }

    // Pre:
    // Post array.size
    public static int size() {
        return length;
    }

    // Pre:
    // Post: false if length == 0 true else
    public static boolean isEmpty() {
        return length == 0;
    }

    // Pre:
    // Post: queue.length = 0 and queue.head = 0 and queue.tail = 0
    public static void clear() {
        array = new Object[2];
        length = 0;
        head = 0;
        tail = 0;
    }
}

package queue;



public class ArrayQueueModule extends AbstractArrayQueue {

    private static int tail = 0;
    private static int head = 0;

    private static int length = 0;

    private static Object[] array = new Object[2];

    private static void expandArrayNeeded() {
        if (head == tail && length != 0) {
            array = expandArray(head, tail, array);
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

    // Pre:
    // Post: array[tail - 1 % array.size]
    public static Object peek() {
        return array[(tail - 1 + array.length) % array.length];
    }

    // Pre: queue.size > 0
    // Post: array[tail] and tail' = tail - 1 % array.size
    public static Object remove() {
        tail = (tail - 1 + array.length) % array.length;
        Object tmp =  array[tail];
        array[tail] = null;
        length--;
        return tmp;
    }

    // Pre: queue.size > 0
    // Post: array[head] head' = head + 1 % array.size
    public static Object dequeue() {
        Object t = array[head];
        array[head] = null;
        head = (head + 1) % array.length;
        length--;
        // printArray();
        return t;
    }

    // Pre:
    // Post: array[head]
    public static Object element() {
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

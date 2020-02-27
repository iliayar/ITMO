package queue;



public class ArrayQueueModule extends AbstractArrayQueue {

    private static int tail = 0;
    private static int head = 0;

    private static int length = 0;

    private static Object[] array = new Object[2];

    private static void printArray() {
        System.err.println(tail + " " + head);
        for(int i = 0; i < array.length; ++i) {
            System.err.print(array[i] + " ");
        }
        System.err.println( );
    }

    public static void enqueue(Object x) {
        array[tail] = x;
        tail = (tail+1) % array.length;
        if(head == tail && length != 0) {
            array = expandArray(head, tail, array);
            head = array.length/2 + head;
        }
        length++;
        // printArray();
    }

    public static void push(Object x) {
        head = (head - 1 + array.length) % array.length;
        array[head] = x;
        if(head == tail && length != 0) {
            array = expandArray(head, tail, array);
            head = array.length/2 + head;
        }
        length++;
    }

    public static Object peek() {
        return array[(tail - 1 + array.length) % array.length];
    }

    public static Object remove() {
        if (length == 0) {
            return null;
        }
        tail = (tail - 1 + array.length) % array.length;
        Object tmp =  array[tail];
        array[tail] = null;
        length--;
        return tmp;
    }

    public static Object dequeue() {
        if(length == 0) {
            return null;
        }
        Object t = array[head];
        array[head] = null;
        head = (head + 1) % array.length;
        length--;
        // printArray();
        return t;
    }

    public static Object element() {
        return array[head];
    }

    public static int size() {
        return length;
    }

    public static boolean isEmpty() {
        return length == 0;
    }
    public static void clear() {
        array = new Object[2];
        length = 0;
        head = 0;
        tail = 0;
    }
}

package queue;



public class ArrayQueueModule {

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
    private static void expandArrayNeeded() {
        if(array[tail] == null) {
            return;
        }
        Object[] temp = new Object[array.length*2];
        System.arraycopy(array, head, temp, array.length + head, array.length - head);
        System.arraycopy(array, 0, temp, 0, tail);
        head = array.length + head;
        array = temp;
    }

    public static void enqueue(Object x) {
        expandArrayNeeded();
        array[tail] = x;
        tail = (tail+1) % array.length;
        length++;
        // printArray();
    }

    public static Object dequeue() {
        if(array[head] == null) {
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

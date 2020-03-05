package queue;

// inv: 0 <= length < array.size and
//      tail != head or length = 0
//      0 <= tail,head < array.size
//      array[tail : head] != null
public class ArrayQueueADT {

    private int tail = 0;
    private int head = 0;

    private int length = 0;

    private Object[] array = new Object[2];

    private static void expandArrayNeeded(ArrayQueueADT queue) {
        if (queue.head == queue.tail && queue.length != 0) {
            Object[] temp = new Object[queue.array.length * 2];
            System.arraycopy(queue.array, queue.head, temp, queue.array.length + queue.head, queue.array.length - queue.head);
            System.arraycopy(queue.array, 0, temp, 0, queue.tail);
            queue.array = temp;
            queue.head = queue.array.length / 2 + queue.head;
        }
    }

    // Pre: queue != null x != null
    // Post: array[tail] = x and tail' = tail + 1 % array.size
    public static void enqueue(ArrayQueueADT queue, Object x) {
        queue.array[queue.tail] = x;
        queue.tail = (queue.tail+1) % queue.array.length;
        expandArrayNeeded(queue);
        queue.length++;
        // printArray();
    }

    // Pre: queue != null x != null
    // Post: array[head'] = x and head' = head - 1 % array.size
    public static void push(ArrayQueueADT queue, Object x) {
        queue.head = (queue.head - 1 + queue.array.length) % queue.array.length;
        queue.array[queue.head] = x;
        expandArrayNeeded(queue);
        queue.length++;
    }

    // Pre: queue != null and queue.size > 0
    // Post: array[tail - 1 % array.size]
    public static Object peek(ArrayQueueADT queue) {
        if (queue.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return queue.array[(queue.tail - 1 + queue.array.length) % queue.array.length];
    }


    // Pre: queue != null and queue.size > 0
    // Post: array[tail] and tail' = tail - 1 % array.size
    public static Object remove(ArrayQueueADT queue) {
        if (queue.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        queue.tail = (queue.tail - 1 + queue.array.length) % queue.array.length;
        Object tmp =  queue.array[queue.tail];
        queue.array[queue.tail] = null;
        queue.length--;
        return tmp;
    }

    // Pre: queue != null and queue.size > 0
    // Post: array[head] head' = head + 1 % array.size
    public static Object dequeue(ArrayQueueADT queue) {
        if(queue.length == 0) {
            throw new RuntimeException("Queue is empty"); 
        }
        Object t = queue.array[queue.head];
        queue.array[queue.head] = null;
        queue.head = (queue.head + 1) % queue.array.length;
        queue.length--;
        // printArray(ArrayQueueADT queue);
        return t;
    }


    // Pre: queue != null and queue.size  > 0
    // Post: array[head]
    public static Object element(ArrayQueueADT queue) {
        if (queue.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return queue.array[queue.head];
    }


    // Pre: queue != null
    // Post array.size
    public static int size(ArrayQueueADT queue) {
        return queue.length;
    }

    // Pre: queue != null
    // Post: false if a - empty true else
    public static boolean isEmpty(ArrayQueueADT queue) {
        return queue.length == 0;
    }

    // Pre: queue != null
    // Post: queue.length = 0 and queue.head = 0 and queue.tail = 0
    public static void clear(ArrayQueueADT queue) {
        queue.array = new Object[2];
        queue.length = 0;
        queue.head = 0;
        queue.tail = 0;
    }
}

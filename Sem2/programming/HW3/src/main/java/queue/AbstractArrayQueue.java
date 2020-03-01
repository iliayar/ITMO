package queue;



public class AbstractArrayQueue {


    protected int tail = 0;
    protected int head = 0;

    protected int length = 0;

    protected Object[] array = new Object[2];

    // Pre: 0 <= head = tail < array.size
    // Post array.size = 2*array.size
    protected static Object[] expandArray(int head, int tail, Object[] array) {
        Object[] temp = new Object[array.length*2];
        System.arraycopy(array, head, temp, array.length + head, array.length - head);
        System.arraycopy(array, 0, temp, 0, tail);
        return temp;
    }
}

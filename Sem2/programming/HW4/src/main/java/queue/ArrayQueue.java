package queue;

public class ArrayQueue extends AbstractQueue {

    private int tail = 0;
    private int head = 0;

    private Object[] array = new Object[2];

    protected static Object[] expandArray(int head, int tail, Object[] array) {
        Object[] temp = new Object[array.length*2];
        System.arraycopy(array, head, temp, array.length + head, array.length - head);
        System.arraycopy(array, 0, temp, 0, tail);
        return temp;
    }

    public void enqueue(Object x) {
        this.array[this.tail] = x;
        this.tail = (this.tail+1) % this.array.length;
        if(this.head == this.tail && this.length != 0) {
            array = expandArray(head, tail, array);
            head = array.length/2 + head;
        }
        this.length++;
    }

    public Object dequeue() {
        Object t = this.array[this.head];
        this.array[this.head] = null;
        this.head = (this.head + 1) % this.array.length;
        this.length--;
        return t;
    }

    public Object element() {
        return this.array[this.head];
    }

    public int size() {
        return this.length;
    }

    public boolean isEmpty() {
        return this.length == 0;
    }
    public void clear() {
        this.array = new Object[2];
        this.length = 0;
        this.head = 0;
        this.tail = 0;
    }

    protected Queue getNewInstance() {
        return new ArrayQueue();
    }

}

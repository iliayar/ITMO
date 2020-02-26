package queue;


// inv: length < array.size and
//      tail != head and
public class ArrayQueue extends AbstractArrayQueue {

    private int tail = 0;
    private int head = 0;

    private int length = 0;

    private Object[] array = new Object[2];

    // Pre: ?
    // Post: array[tail] = x
    public void enqueue(Object x) {
        if(head == tail && length != 0) {
            array = expandArray(head, tail, array);
            head = array.length/2 + head;
        }
        this.array[this.tail] = x;
        this.tail = (this.tail+1) % this.array.length;
        this.length++;
        // printArray();
    }

    // Pre:  
    public Object dequeue() {
        if(this.array[this.head] == null) {
            return null;
        }
        Object t = this.array[this.head];
        this.array[this.head] = null;
        this.head = (this.head + 1) % this.array.length;
        this.length--;
        // printArray();
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
}

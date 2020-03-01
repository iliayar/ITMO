package queue;


// inv: length < array.size and
//      tail != head and
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

    // Pre: ?
    // Post: array[tail] = x
    public void enqueue(Object x) {
        this.array[this.tail] = x;
        this.tail = (this.tail+1) % this.array.length;
        if(this.head == this.tail && this.length != 0) {
            array = expandArray(head, tail, array);
            head = array.length/2 + head;
        }
        this.length++;
        // printArray();
    }

    public void push(Object x) {
        head = (head - 1 + this.array.length) % this.array.length;
        this.array[head] = x;
        if(this.head == this.tail && this.length != 0) {
            this.array = expandArray(this.head, this.tail, this.array);
            this.head = this.array.length/2 + this.head;
        }
        this.length++;
    }

    public Object peek() {
        return this.array[(tail - 1 + this.array.length) % this.array.length];
    }

    public Object remove() {
        if(this.length == 0) {
            return null;
        }
        this.tail = (this.tail - 1 + this.array.length) % this.array.length;
        Object tmp =  this.array[this.tail];
        this.array[this.tail] = null;
        this.length--;
        return tmp;
    }

    public Object dequeue() {
        if(this.length == 0) {
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

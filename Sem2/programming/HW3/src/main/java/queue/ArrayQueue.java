package queue;


// inv: length < array.size and
//      tail != head and
public class ArrayQueue {

    private int tail = 0;
    private int head = 0;

    private int length = 0;

    private Object[] array = new Object[2];

    private void expandArrayNeeded() {
        if(tail != head || length == 0) {
            return;
        }
        Object[] temp = new Object[this.array.length*2];
        System.arraycopy(this.array, this.head, temp, this.array.length + this.head, this.array.length - this.head);
        System.arraycopy(this.array, 0, temp, 0, this.tail);
        this.head = this.array.length + this.head;
        this.array = temp;
    }

    // Pre: ?
    // Post: array[tail] = x
    public void enqueue(Object x) {
        expandArrayNeeded();
        this.array[this.tail] = x;
        this.tail = (this.tail+1) % this.array.length;
        this.length++;
        // printArray();
    }

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

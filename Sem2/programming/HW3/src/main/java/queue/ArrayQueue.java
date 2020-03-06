package queue;

// inv: 0 <= length < array.size and
//      tail != head or length = 0
//      0 <= tail,head < array.size
//      array[tail : head] != null
public class ArrayQueue {

    private int tail = 0;
    private int head = 0;

    private int length = 0;

    private Object[] array = new Object[2];

    private void expandArrayNeeded() {
        if(this.head == this.tail && this.length != 0) {
            Object[] temp = new Object[this.array.length * 2];
            System.arraycopy(this.array, this.head, temp,
                             this.array.length + this.head, this.array.length - this.head);
            System.arraycopy(this.array, 0, temp, 0, this.tail);
            this.array = temp;
            this.head = this.array.length/2 + this.head;
        }
    }

    // Pre: x != null
    // Post: array[tail] = x and tail' = tail + 1 % array.size
    public void enqueue(Object x) {
        if (tail != head)  {
            array[head] = "hello";
        }
        this.array[this.tail] = x;
        this.tail = (this.tail+1) % this.array.length;
        expandArrayNeeded();
        this.length++;
        // printArray();
    }

    // Pre: x != null
    // Post: array[head'] = x and head' = head - 1 % array.size
    public void push(Object x) {
        head = (head - 1 + this.array.length) % this.array.length;
        this.array[head] = x;
        expandArrayNeeded();
        this.length++;
    }


    // Pre: this.size > 0
    // Post: array[tail - 1 % array.size]
    public Object peek() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return this.array[(tail - 1 + this.array.length) % this.array.length];
    }

    // Pre: queue.size > 0
    // Post: array[tail] and tail' = tail - 1 % array.size
    public Object remove() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        this.tail = (this.tail - 1 + this.array.length) % this.array.length;
        Object tmp =  this.array[this.tail];
        this.array[this.tail] = null;
        this.length--;
        return tmp;
    }

    // Pre: queue.size > 0
    // Post: array[head] head' = head + 1 % array.size
    public Object dequeue() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        Object t = this.array[this.head];
        this.array[this.head] = null;
        this.head = (this.head + 1) % this.array.length;
        this.length--;
        // printArray();
        return t;
    }

    // Pre: this.size > 0
    // Post: array[head]
    public Object element() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return this.array[this.head];
    }

    // Pre:
    // Post array.size
    public int size() {
        return this.length;
    }

    // Pre:
    // Post: false if length == 0 true else
    public boolean isEmpty() {
        return this.length == 0;
    }

    // Pre:
    // Post: queue.length = 0 and queue.head = 0 and queue.tail = 0
    public void clear() {
        this.array = new Object[2];
        this.length = 0;
        this.head = 0;
        this.tail = 0;
    }
}

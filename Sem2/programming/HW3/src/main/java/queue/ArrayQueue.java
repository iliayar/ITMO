package queue;

// inv: queue = {q1(tail), q2, .. , qn(head)}
//      |q| >= 0
public class ArrayQueue {

    private int tail = 0;
    private int head = 0;

    private int length = 0;

    private Object[] array = new Object[2];

    // Pre: 
    // Post: |queue'| = 2*|queue| if array.length == |queue|
    private void expandArrayNeeded() {
        if (this.head == this.tail && this.length != 0) {
            Object[] temp = new Object[this.array.length * 2];
            System.arraycopy(this.array, this.head, temp, this.array.length + this.head, this.array.length - this.head);
            System.arraycopy(this.array, 0, temp, 0, this.tail);
            this.array = temp;
            this.head = this.array.length / 2 + this.head;
        }
    }

    // Pre: x != null queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {x(tail), q1, q2, .. , qn(head)}
    public void enqueue(Object x) {
        if (tail != head)  {
            array[head] = "hello";
        }
        this.array[this.tail] = x;
        this.tail = (this.tail + 1) % this.array.length;
        expandArrayNeeded();
        this.length++;
        // printArray();
    }

    // Pre: x != null queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {q1(tail), q2, .., qn, x(head)}
    public void push(Object x) {
        head = (head - 1 + this.array.length) % this.array.length;
        this.array[head] = x;
        expandArrayNeeded();
        this.length++;
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: q1
    public Object peek() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return this.array[(tail - 1 + this.array.length) % this.array.length];
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {q2(tail), q3, .., qn(head)}
    public Object remove() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        this.tail = (this.tail - 1 + this.array.length) % this.array.length;
        Object tmp = this.array[this.tail];
        this.array[this.tail] = null;
        this.length--;
        return tmp;
    }

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {q1(tail), q2, .., q(n-1)(head)}
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

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: qn
    public Object element() {
        if (this.length == 0) {
            throw new RuntimeException("Queue is empty");
        }
        return this.array[this.head];
    }

    // Pre:
    // Post |queue|
    public int size() {
        return this.length;
    }

    // Pre:
    // Post: true if |queue| == 0 else false
    public boolean isEmpty() {
        return this.length == 0;
    }

    // Pre:
    // Post: queue = {} |queue| = 0
    public void clear() {
        this.array = new Object[2];
        this.length = 0;
        this.head = 0;
        this.tail = 0;
    }
}

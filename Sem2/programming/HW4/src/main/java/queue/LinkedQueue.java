package queue;



public class LinkedQueue extends AbstractQueue {

    private Node head;
    private Node tail;

    public LinkedQueue() {
        head = null;
        tail = null;
        length = 0;
    }

    @Override
    public void enqueue(Object x) {
        Node t = new Node(null, x);
        length++;
        if (length - 1 == 0) {
            tail = t;
            head = t;
            return;
        }
        tail.prev = t;
        tail = t;
    }

    @Override
    public Object element() {
        return head.value;
    }

    @Override
    public Object dequeue() {
        Node t = head;
        head = head.prev;
        length--;
        return t.value;
    }


    @Override
    public void clear() {
        head = null;
        tail = null;
        length = 0;
    }


    private class Node {
        Node prev;
        Object value;

        Node(Node prev, Object value) {
            this.prev = prev;
            this.value = value;
        }
    }


}

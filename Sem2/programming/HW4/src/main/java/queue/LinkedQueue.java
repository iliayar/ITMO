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
        if (length == 0) {
            tail = t;
            head = t;
            length++;
            return;
        }
        tail.prev = t;
        tail = t;
        length++;
    }

    @Override
    public Object element() {
        return head.value;
    }

    @Override
    public Object dequeue() {
        if (length == 0) {
            return null;
        }
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

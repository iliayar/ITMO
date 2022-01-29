package msqueue;

import java.util.Currency;

import kotlinx.atomicfu.AtomicRef;

public class MSQueue implements Queue {
    private AtomicRef<Node> head;
    private AtomicRef<Node> tail;

    public MSQueue() {
        Node dummy = new Node(0);
        this.head = new AtomicRef<MSQueue.Node>(dummy);
        this.tail = new AtomicRef<MSQueue.Node>(dummy);
    }

    @Override
    public void enqueue(int x) {
        Node newTail = new Node(x);
        while (true) {
            Node curTail = tail.getValue();
            Node next = curTail.next.getValue();
            if (curTail == tail.getValue()) {
                if (next == null) {
                    if (curTail.next.compareAndSet(next, newTail)) {
                        tail.compareAndSet(curTail, newTail);
                        return;
                    }
                } else {
                    tail.compareAndSet(curTail, curTail.next.getValue());
                }
            }
        }
    }

    @Override
    public int dequeue() {
        return peekImpl(true);
    }

    @Override
    public int peek() {
        return peekImpl(false);
    }

    private int peekImpl(boolean doDelete) {
        while (true) {
            Node curHead = head.getValue();
            Node curTail = tail.getValue();
            Node next = curHead.next.getValue();

            if (curHead == head.getValue()) {
                if (curHead == curTail) {
                    if (next == null) {
                        return Integer.MIN_VALUE;
                    }
                    tail.compareAndSet(curTail, next);
                } else {
                    if (doDelete) {
                        if (head.compareAndSet(curHead, next)) {
                            return next.x;
                        }
                    } else {
                        return next.x;
                    }
                }
            }
        }
    }

    private class Node {
        final int x;
        AtomicRef<Node> next;

        Node(int x) {
            this.x = x;
            next = new AtomicRef<>(null);
        }
    }
}

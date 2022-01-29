package stack;

import kotlinx.atomicfu.AtomicIntArray;
import kotlinx.atomicfu.AtomicRef;
import java.util.concurrent.ThreadLocalRandom;;

public class StackImpl implements Stack {

    public static int WAIT_ITERATIONS = 10;
    public static int ELIMINATION_ARRAY_SIZE = 3;
    public static int ELIMINATION_POP_RANGE = 1;
    public static int ELIMINATION_PUSH_RANGE = 1;
    public static int EMPTY_VALUE = Integer.MIN_VALUE + 1;

    private static class Node {
        final AtomicRef<Node> next;
        final int x;

        Node(int x, Node next) {
            this.next = new AtomicRef<>(next);
            this.x = x;
        }
    }

    private static class EliminationArray {

        AtomicIntArray array;

        private int arraySize;

        public EliminationArray(int size) {
            arraySize = size;
            array = new AtomicIntArray(arraySize);
            for(int i = 0; i < size; ++i) {
                array.get(i).setValue(EMPTY_VALUE);
            }
        }

        public boolean push(int x) {
            int index = ThreadLocalRandom.current().nextInt() % arraySize;
            int left = Math.max(0, index - ELIMINATION_PUSH_RANGE);
            int right = Math.min(arraySize - 1, index + ELIMINATION_PUSH_RANGE);

            for(int i = left; i <= right; ++i) {
                if (array.get(i).compareAndSet(EMPTY_VALUE, x)) {
                    for(int j = 0; j < WAIT_ITERATIONS; ++j) {
                        if (array.get(i).compareAndSet(EMPTY_VALUE, EMPTY_VALUE)) {
                            return true;
                        }
                    }
                    return !array.get(i).compareAndSet(x, EMPTY_VALUE);
                }
            }

            return false;
        }

        public int pop() {
            int index = ThreadLocalRandom.current().nextInt() % arraySize;
            int left = Math.max(0, index - ELIMINATION_POP_RANGE);
            int right = Math.min(arraySize - 1, index + ELIMINATION_POP_RANGE);

            for(int i = left; i <= right; ++i) {
                int value = array.get(i).getValue();
                if (value != EMPTY_VALUE && array.get(i).compareAndSet(value, EMPTY_VALUE)) {
                    return value;
                }
            }

            return EMPTY_VALUE;
        }
    }

    // head pointer
    private AtomicRef<Node> head = new AtomicRef<>(null);
    private EliminationArray eliminationArray = new EliminationArray(ELIMINATION_ARRAY_SIZE);

    @Override
    public void push(int x) {
        if (x != EMPTY_VALUE && eliminationArray.push(x)) {
            return;
        }

        while (true) {
            Node curHead = head.getValue();
            Node newHead = new Node(x, curHead);

            if (head.compareAndSet(curHead, newHead)) {
                return;
            }
        }
    }

    @Override
    public int pop() {
        int value = eliminationArray.pop();
        if (value != EMPTY_VALUE) {
            return value;
        }

        while (true) {
            Node curHead = head.getValue();
            if (curHead == null) {
                return Integer.MIN_VALUE;
            }

            if (head.compareAndSet(curHead, curHead.next.getValue())) {
                return curHead.x;
            }
        }
    }
}

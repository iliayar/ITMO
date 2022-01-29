package linked_list_set;

import kotlinx.atomicfu.AtomicRef;

public class SetImpl implements Set {

    private class NodeOrRemoved {
    }

    private class MutableFlag {
        boolean flag = false;
    }

    private class Removed extends NodeOrRemoved {
        private final Node node;

        Removed(Node node) {
            this.node = node;
        }
    };

    private class Node extends NodeOrRemoved {
        AtomicRef<NodeOrRemoved> next;
        int x;

        Node(int x, Node next) {
            this.next = new AtomicRef<NodeOrRemoved>(next);
            this.x = x;
        }
    }

    private class Window {
        Node cur, next;
    }

    private final Node head = new Node(Integer.MIN_VALUE, new Node(Integer.MAX_VALUE, null));

    private Node getNode(NodeOrRemoved node, MutableFlag flag) {
        if (node == null) {
            flag.flag = false;
            return null;
        }
        if (node instanceof Removed) {
            flag.flag = true;
            return ((Removed) node).node;
        }
        flag.flag = false;
        return ((Node) node);
    }

    /**
     * Returns the {@link Window}, where cur.x < x <= next.x
     */
    private Window findWindow(int x) {
        int it = 0;
        int helped = 0;
        int find_removed = 0;
        Window w = new Window();
        MutableFlag removed = new MutableFlag();
        retry: while (true) {
            it++;
            if (it > 1_000_000_000) {
                System.err.println("findWindow stuck? helped: " + helped + " find removed: " + find_removed);
                System.exit(1);
            }
            w.cur = head;
            w.next = getNode(w.cur.next.getValue(), removed);
            while (w.next.x < x) {
                Node node = getNode(w.next.next.getValue(), removed);
                if (removed.flag) {
                    if (!w.cur.next.compareAndSet(w.next, node)) {
                        helped++;
                        continue retry;
                    }
                } else {
                    w.cur = w.next;
                }
                w.next = node;
            }
            Node node = getNode(w.next.next.getValue(), removed);
            if (!removed.flag) {
                return w;
            } else {
                w.cur.next.compareAndSet(w.next, node);
            }
        }
    }

    @Override
    public boolean add(int x) {
        while (true) {
            Window w = findWindow(x);
            if (w.next.x == x) {
                return false;
            }
            Node node = new Node(x, w.next);
            if (w.cur.next.compareAndSet(w.next, node)) {
                return true;
            }
        }
    }

    @Override
    public boolean remove(int x) {
        MutableFlag removed = new MutableFlag();
        while (true) {
            Window w = findWindow(x);
            if (w.next.x != x) {
                return false;
            }
            Node node = getNode(w.next.next.getValue(), removed);
            Removed removedNode = new Removed(node);
            if (w.next.next.compareAndSet(node, removedNode)) {
                 w.cur.next.compareAndSet(w.next, node);
                return true;
            }
        }
    }

    @Override
    public boolean contains(int x) {
        Window w = findWindow(x);
        boolean res = w.next.x == x;
        return res;
    }
}

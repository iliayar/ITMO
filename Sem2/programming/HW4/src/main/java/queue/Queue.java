package queue;



public interface Queue {
    public void enqueue(Object x);
    public Object element();
    public Object dequeue();
    public int size();
    public boolean isEmpty();
    public void clear();
}

package queue;


// inv: size >= 0
public interface Queue {

    // Pre: x != null
    // Post: x в конце очереди
    public void enqueue(Object x);

    // Pre: size > 0
    // Post: result == элемент в начале очереди
    public Object element();

    // Pre: size > 0
    // Post: result == элемент из начала очереди and удаление 1 элемента из начала
    public Object dequeue();

    // Pre:
    // Post: result == size
    public int size();

    // Pre:
    // Post result == true if size == 0 else false
    public boolean isEmpty();

    // Pre:
    // Post: size == 0
    public void clear();
}

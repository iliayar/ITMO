package queue;

import java.util.function.Function;
import java.util.function.Predicate;

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

    // Pre: predicate != null
    // Post: Очередь в которой каждый элемент удовлетворяет предикату, порядок сохранен, того же типа
    public Queue filter(Predicate<Object> predicate);

    // Pre: function != null
    // Post: Очередь, к каждому элементу применена функция, порядок сохранен, того же типа
    public Queue map(Function<Object, Object> function);
}

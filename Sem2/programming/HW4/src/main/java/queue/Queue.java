package queue;

import java.util.function.Function;
import java.util.function.Predicate;

// inv: size >= 0
public interface Queue {

    // Pre: x != null queue = {q1(tail), q1, .., qn(head)}
    // Post: queue' = {x(tail), q1, q2, .. , qn(head)}
    public void enqueue(Object x);

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: qn
    public Object element();

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: queue' = {q1(tail), q2, .., q(n-1)(head)}
    public Object dequeue();

    // Pre:
    // Post |queue|
    public int size();

    // Pre:
    // Post: true if |queue| == 0 else false
    public boolean isEmpty();

    // Pre:
    // Post: queue = {} |queue| = 0
    public void clear();

    // Pre: predicate != null
    // Post: queue' = {q in queue: predicate(q) == true}
    public Queue filter(Predicate<Object> predicate);

    // Pre: function != null
    // Post: queue' = {function(q): q in queue }
    public Queue map(Function<Object, Object> function);
}

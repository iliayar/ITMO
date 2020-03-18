package queue;

import java.util.function.Function;
import java.util.function.Predicate;

// inv: queue = {q1(tail), q2, .., qn(head)}
//      |queue| >= 0
public interface Queue {

    // Pre: x != null queue = {q1(tail), q1, .., qn(head)}
    // Post: queue' = {x(tail), q1, q2, .. , qn(head)}
    public void enqueue(Object x);

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: R = qn
    public Object element();

    // Pre: |queue| > 0 queue = {q1(tail), q2, .., qn(head)}
    // Post: R = qn and queue' = {q1(tail), q2, .., q(n-1)(head)}
    public Object dequeue();

    // Pre:
    // Post R = |queue|
    public int size();

    // Pre:
    // Post: R = |queue| == 0
    public boolean isEmpty();

    // Pre:
    // Post: queue = {} |queue| = 0
    public void clear();

    // Pre: predicate != null
    // Post: R = {q in queue: predicate(q) == true} and
    //       queue = {q1(tail), q2, .., qn(head)}
    //       forall q in queue: predicate(q) == true => q in R
    //       order the same
    default Queue filter(Predicate<Object> predicate) {
        return new ArrayQueue();
    }

    // Pre: function != null
    // Post: R = {function(q): q in queue } and
    //       queue = {q1(tail), q2, .., qn(head)}
    //       order the same
    public Queue map(Function<Object, Object> function);
}

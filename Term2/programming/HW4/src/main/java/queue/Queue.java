package queue;

import java.util.function.Function;
import java.util.function.Predicate;

// inv: queue = {q1, q2, .., qn}
//      |queue| >= 0
public interface Queue {

    // Pre: x != null queue = {q1, q1, .., qn}
    // Post: queue' = {x, q1, q2, .. , qn}
    public void enqueue(Object x);

    // Pre: |queue| > 0 queue = {q1, q2, .., qn}
    // Post: R = qn
    public Object element();

    // Pre: |queue| > 0 queue = {q1, q2, .., qn}
    // Post: R = qn and queue' = {q1, q2, .., q(n-1)}
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
    //       queue = {q1, q2, .., qn}
    //       if qi befort qj in queue and predicate(qi) == true and predicte(qj) == true =>
    //       => qi before qj in R
    default Queue filter(Predicate<Object> predicate) {
        return new ArrayQueue();
    }

    // Pre: function != null
    // Post: R = {function(q): q in queue } and
    //       queue = {q1, q2, .., qn}
    //       if qi befort qj in queue =>
    //       => qi before qj in R
    public Queue map(Function<Object, Object> function);
}

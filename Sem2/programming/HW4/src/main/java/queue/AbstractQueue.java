package queue;

import java.util.function.Function;
import java.util.function.Predicate;

abstract class AbstractQueue implements Queue {
    protected int length;

    @Override
    public int size() {
        return length;
    }

    @Override
    public boolean isEmpty() {
        return length == 0;
    }

    @Override
    public Queue filter(Predicate<Object> predicate) {
        Queue resQueue = this.getNewInstance();

        for(int i = 0, end = this.size(); i < end; ++i) {
            Object x = this.dequeue();
            if(predicate.test(x)) {
                resQueue.enqueue(x);
            }
            this.enqueue(x);
        }

        return resQueue;
    }

    @Override
    public Queue map(Function<Object, Object> function) {
        Queue resQueue = this.getNewInstance();

        for (int i = 0, end = this.size(); i < end; ++i) {
            Object x = this.dequeue();
            resQueue.enqueue(function.apply(x));
            this.enqueue(x);
        }

        return resQueue;
    }


    protected abstract Queue getNewInstance();

}

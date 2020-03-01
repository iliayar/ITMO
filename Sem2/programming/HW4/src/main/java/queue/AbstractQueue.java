package queue;




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
}

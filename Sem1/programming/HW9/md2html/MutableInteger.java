package md2html;

public class MutableInteger {
    private int val;

    public MutableInteger(int val) {
        this.val = val;
    }

    public MutableInteger() {
        this.val = 0;
    }

    public void inc() {
        val++;
    }

    public int val() {
        return val;
    }

    public void sub(int val) {
        this.val -= val;
    }

    public void add(int val) {
        this.val += val;
    }

    public void setVal(int val) {
        this.val = val;
    }

    @Override
    public String toString() {
        return Integer.toString(val);
    }
}

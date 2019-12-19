package expression;

public class Const extends Operand {

    int value;

    public Const(int v) {
        this.value = v;
    }

    public Const(long v) {
        this.value = (int)v;
    }

    @Override
    protected String getSymbol() {
        return Integer.toString(value);
    }

    @Override
    protected int getValue(int x) {
        return value;
    }

    @Override
    protected long getValue(long x, long y, long z) {
        return value;
    }


    @Override
    protected int getValue(int x, int y, int z) {
        return value;
    }

//    @Override
    public int getPrior() {
        return 0;
    }
}

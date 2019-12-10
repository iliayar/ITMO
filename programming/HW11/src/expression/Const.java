package expression;

public class Const extends Operand {

    int value;

    public Const(int v) {
        this.value = v;
    }

    @Override
    protected String getSymbol() {
        return Integer.toString(value);
    }

    @Override
    protected int getValue(int x) {
        return value;
    }

//    @Override
    public int getPrior() {
        return 0;
    }
}

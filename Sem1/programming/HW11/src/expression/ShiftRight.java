package expression;

public class ShiftRight extends Operation {
    public ShiftRight(Expression a, Expression b) {
        super(a, b);
    }

    @Override
    public String getSymbol() {
        return ">>";
    }

    @Override
    protected int eval(int a, int b) throws IntegerOverflowException, DivisonByZeroException {
        return a >> b;
    }


    @Override
    public int getPrior() {
        return 3;
    }

    @Override
    public boolean isCommutative() {
        return false;
    }
}

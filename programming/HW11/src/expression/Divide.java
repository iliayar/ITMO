package expression;

import java.math.BigInteger;

public class Divide extends Operation {
    public Divide(CommonExpression a, CommonExpression b) {
        super(a, b);
    }

    @Override
    protected String getSymbol() {
        return "/";
    }

    @Override
    protected int eval(int a, int b) {
        return a / b;
    }

    @Override
    public int getPrior() {
        return 1;
    }

    @Override
    public boolean isCommutative() {
        return false;
    }

    @Override
    public boolean isIntSafe() {
        return false;
    }
}

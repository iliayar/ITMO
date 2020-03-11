package expression;

import java.math.BigInteger;

public class Divide extends Operation {
    public Divide(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "/";
    }

    @Override
    protected Number eval(Number a, Number b) {
        return calc.divide(a, b);
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

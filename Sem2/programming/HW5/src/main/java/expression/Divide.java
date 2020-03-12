package expression;

import java.math.BigInteger;

public class Divide<T extends Number> extends Operation<T> {
    public Divide(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "/";
    }

    @Override
    protected T eval(T a, T b) {
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

package expression;

import java.math.BigInteger;

public class Negate<T extends Number> extends UnaryOperation<T> {
    public Negate(CommonExpression<T> a, Calculator<T> calc) {
        super(a, calc);
    }

    @Override
    public String getSymbol() {
        return "-";
    }

    @Override
    public CommonExpression getFirst() {
        return null;
    }

    @Override
    public CommonExpression getSecond() {
        return null;
    }

    protected T eval(T a) {
        return calc.negate(a);
    }

    @Override
    public int getPrior() {
        return 0;
    }
}

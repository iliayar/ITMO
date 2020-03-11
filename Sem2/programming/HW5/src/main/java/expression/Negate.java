package expression;

import java.math.BigInteger;

public class Negate extends UnaryOperation {
    public Negate(Expression a, Calculator calc) {
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

    protected <T extends Number> T eval(T a) {
        return calc.negate(a);
    }

    @Override
    public int getPrior() {
        return 0;
    }
}

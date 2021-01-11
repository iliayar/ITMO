package expression;

import java.math.BigInteger;

public class Multiply<T extends Number> extends Operation<T> {
    public Multiply(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "*";
    }

    protected T eval(T a, T b) {
        return calc.multiply(a, b);
    }


    @Override
    public int getPrior() {
        return 1;
    }
    @Override
    public boolean isCommutative() {
        return true;
    }
}

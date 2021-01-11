package expression;

import java.math.BigInteger;

public class Add<T extends Number> extends Operation<T> {

    public Add(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a,b,calc);
    }

    @Override
    public String getSymbol() {
        return "+";
    }

    @Override
    protected T eval(T a, T b) {
        return calc.add(a,b);
    }

    @Override
    public int getPrior() {
        return 2;
    }

    @Override
    public boolean isCommutative() {
        return true;
    }

}

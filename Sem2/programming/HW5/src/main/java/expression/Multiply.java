package expression;

import java.math.BigInteger;

public class Multiply extends Operation {
    public Multiply(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "*";
    }

    protected <T extends Number> T eval(T a, T b) {
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

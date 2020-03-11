package expression;

import java.math.BigInteger;

public class Add extends Operation {

    public Add(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a,b, calc);
    }

    @Override
    public String getSymbol() {
        return "+";
    }

    @Override
    protected Number eval(Number a, Number b) {
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

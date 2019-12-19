package expression;

import java.math.BigInteger;

public class Digits extends UnaryOperation {

    public Digits(Expression a) {
        super(a);
    }

    @Override
    protected String getSymbol() {
        return "digits ";
    }

    @Override
    protected int eval(int a) {
        a = a < 0 ? -a : a;

        int res = 0;
        while(a > 0) {
            res += a%10;
            a /=10;
        }
        return res;
    }

    @Override
    protected BigInteger eval(BigInteger a) {
        a = a.compareTo(BigInteger.ZERO) < 0 ? a.multiply(BigInteger.valueOf(-1)) : a;

        BigInteger res = BigInteger.ZERO;
        while(a.compareTo(BigInteger.ZERO) > 0) {
            res = res.add(a.mod(BigInteger.valueOf(10)));
            a = a.divide(BigInteger.valueOf(10));
        }
        return res;

    }


    @Override
    public int getPrior() {
        return 0;
    }
}

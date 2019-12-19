package expression;

import java.math.BigInteger;

public class Reverse extends UnaryOperation {
    public Reverse(Expression a) {
        super(a);
    }

    @Override
    protected String getSymbol() {
        return "reverse ";
    }

    @Override
    protected int eval(int a) {
//        System.out.println("Reversing int " + a);
        boolean isMinus = a < 0;
        a = a < 0 ? -a : a;
        int res = 0;
        while(a > 0) {
            res = res*10 + a%10;
            a /= 10;
        }

        return isMinus ? -res : res;
    }

    @Override
    protected BigInteger eval(BigInteger a) {
        boolean isMinus = a.compareTo(BigInteger.ZERO) < 0;
//        a = a < 0 ? -a : a;
        a = a.abs();
        BigInteger res = BigInteger.ZERO;
        while(a.compareTo(BigInteger.ZERO) > 0) {
            res = res.multiply(BigInteger.valueOf(10)).add(a.mod(BigInteger.valueOf(10)));
            a = a.divide(BigInteger.valueOf(10));
        }

        return isMinus ? res.multiply(BigInteger.valueOf(-1)) : res;
    }


    @Override
    public int getPrior() {
        return 0;
    }
}

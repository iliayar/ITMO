package expression;

import java.math.BigInteger;

public class BigIntegerCalculator implements Calculator<BigInteger> {
    public BigInteger add(BigInteger a, BigInteger b) {
        return a.add(b);
    }

    public BigInteger multiply(BigInteger a, BigInteger b) {
        return a.multiply(b);
    }

    public BigInteger divide(BigInteger a, BigInteger b) {
        return a.divide(b);
    }

    public BigInteger subtract(BigInteger a, BigInteger b) {
        return a.subtract(b);
    }

    public BigInteger negate(BigInteger a) {
        return a.multiply(BigInteger.valueOf(-1));
    }
    public BigInteger parseNumber(String s) {
        BigInteger n = BigInteger.ZERO;
        for(int i = 0; i < s.length(); ++i) {
            if(s.charAt(i) == '-') {
                continue;
            }
            n = n.multiply(BigInteger.valueOf(10)).add(BigInteger.valueOf(s.charAt(i) - '0'));
        }
        if(s.charAt(0) == '-') {
            n = n.multiply(BigInteger.valueOf(-1));
        }
        return n;
    }
}


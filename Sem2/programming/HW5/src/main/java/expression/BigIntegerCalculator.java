package expression;

import java.math.BigInteger;

// public class BigIntegerCalculator implements Calculator<BigInteger> {
public class BigIntegerCalculator extends AbstractCalculator<BigInteger> {

    @Override
    public BigInteger add(BigInteger a, BigInteger b) {
        return a.add(b);
    }

    @Override
    public BigInteger multiply(BigInteger a, BigInteger b) {
        return a.multiply(b);
    }

    @Override
    public BigInteger divide(BigInteger a, BigInteger b) {
        checkDivide(a, b, null, null);
        return a.divide(b);
    }

    @Override
    public BigInteger subtract(BigInteger a, BigInteger b) {
        return a.subtract(b);
    }

    @Override
    public BigInteger negate(BigInteger a) {
        return a.multiply(BigInteger.valueOf(-1));
    }
    
    @Override
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

    @Override
    public BigInteger valueOf(int n) {
        return BigInteger.valueOf(n);
    }

    @Override
    public int compareTo(BigInteger n, BigInteger a) {
        return n.compareTo(a);
    }

	@Override
	public BigInteger count(BigInteger a) {
		return BigInteger.valueOf(a.bitCount());
	}

}


package expression;

import java.math.BigInteger;

// public class IntegerCalculator implements Calculator<Integer> {
public class IntegerCalculator extends AbstractCalculator<Integer> {


    public IntegerCalculator(boolean checked) {
        super(checked);
    }

    public IntegerCalculator() {
        super();
    }

    @Override
    public Integer add(Integer a, Integer b) {
        checkAdd(a, b, Integer.MAX_VALUE, Integer.MIN_VALUE);
        return a + b;
    }

    @Override
    public Integer divide(Integer a, Integer b) {
        checkDivide(a, b, Integer.MAX_VALUE, Integer.MIN_VALUE);
        return a / b;
    }

    @Override
    public Integer multiply(Integer a, Integer b) {
        checkMultiply(a, b, Integer.MAX_VALUE, Integer.MIN_VALUE);
        return a * b;
    }

    @Override
    public Integer negate(Integer a) {
        checkNegate(a, Integer.MAX_VALUE, Integer.MIN_VALUE);
        return -a;
    }

    @Override
    public Integer parseNumber(String s) {
        return Integer.parseInt(s);
    }

    @Override
    public Integer subtract(Integer a, Integer b) {
        checkSubtract(a, b, Integer.MAX_VALUE, Integer.MIN_VALUE);
        return a - b;
    }

    @Override
    public Integer valueOf(int n) {
        return Integer.valueOf(n);
    }

    @Override
    public int compareTo(Integer n, Integer a) {
        return Integer.compare(n, a);
    }

	@Override
	public Integer count(Integer a) {
      if( a == null) {
          return null;
      }
		return Integer.bitCount(a);
	}
}

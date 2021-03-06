package expression;



// public class LongCalculator implements Calculator<Long> {
public class LongCalculator extends AbstractCalculator<Long> {


    public LongCalculator(boolean checked) {
        super(checked);
    }

    public LongCalculator() {
        super();
    }

    @Override
    public Long add(Long a, Long b) {
        checkAdd(a, b, Long.MAX_VALUE, Long.MIN_VALUE);
        return a + b;
    }

    @Override
    public Long divide(Long a, Long b) {
        checkDivide(a, b, Long.MAX_VALUE, Long.MIN_VALUE);
        return a / b;
    }

    @Override
    public Long multiply(Long a, Long b) {
        checkMultiply(a, b, Long.MAX_VALUE, Long.MIN_VALUE);
        return a * b;
    }

    @Override
    public Long negate(Long a) {
        checkNegate(a, Long.MAX_VALUE, Long.MIN_VALUE);
        return -a;
    }

    @Override
    public Long parseNumber(String s) {
        return Long.parseLong(s);
    }

    @Override
    public Long subtract(Long a, Long b) {
        checkSubtract(a, b, Long.MAX_VALUE, Long.MIN_VALUE);
        return a - b;
    }

    @Override
    public Long valueOf(int n) {
        return Long.valueOf(n);
    }

    @Override
    public int compareTo(Long n, Long a) {
        return Long.compare(n, a);
    }

	@Override
	public Long count(Long a) {
      return valueOf(Long.bitCount(a.longValue()));
	}
}

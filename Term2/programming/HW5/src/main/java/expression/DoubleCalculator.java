package expression;



// public class DoubleCalculator implements Calculator<Double> {
public class DoubleCalculator extends AbstractCalculator<Double> {

    @Override
    public Double add(Double a, Double b) {
        return a + b;
    }

    @Override
    public Double divide(Double a, Double b) {
        return a / b;
    }

    @Override
    public Double multiply(Double a, Double b) {
        return a * b;
    }

    @Override
    public Double subtract(Double a, Double b) {
        return a - b;
    }
    @Override
    public Double negate(Double a) {
        return -a;
    }

    @Override
    public Double parseNumber(String s) {
        return Double.parseDouble(s);
    }


    @Override
    public Double valueOf(int n) {
        return (double) n;
    }

    @Override
    public int compareTo(Double n, Double a) {
        return Double.compare(n, a);
    }

	@Override
	public Double count(Double a) {
      return (double) Long.bitCount(Double.doubleToLongBits(a));
	}

}

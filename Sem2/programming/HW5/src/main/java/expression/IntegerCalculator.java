package expression;



public class IntegerCalculator implements Calculator<Integer> {

	@Override
	public Integer add(Integer a, Integer b) {
		return a + b;
	}

	@Override
	public Integer divide(Integer a, Integer b) {
		return a / b;
	}

	@Override
	public Integer multiply(Integer a, Integer b) {
		return a * b;
	}

	@Override
	public Integer negate(Integer a) {
		return -a;
	}

	@Override
	public Integer parseNumber(String s) {
		return Integer.parseInt(s);
	}

	@Override
	public Integer subtract(Integer a, Integer b) {
		return a - b;
	}
}

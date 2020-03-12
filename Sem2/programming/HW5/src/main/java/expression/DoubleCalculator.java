package expression;



public class DoubleCalculator implements Calculator<Double> {

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
    public Double negate(Double a) {
        return -a;
    }

    @Override
    public Double parseNumber(String s) {
        return Double.parseDouble(s);
    }

    @Override
    public Double subtract(Double a, Double b) {
        return a - b;
    }
}

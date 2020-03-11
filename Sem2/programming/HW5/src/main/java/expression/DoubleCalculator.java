package expression;

import expression.Calculator;

public class DoubleCalculator implements Calculator<Double> {

    public Double add(Double a, Double b) {
        return a + b;
    }

    public Double multiply(Double a, Double b) {
        return a * b;
    }

    public Double divide(Double a, Double b) {
        return a / b;
    }

    public Double substract(Double a, Double b) {
        return a - b;
    }

    public Double negate(Double a) {
        return -a;
    }

    public Double parseNumber(String s) {
        return Double.parseDouble(s);
    }

}

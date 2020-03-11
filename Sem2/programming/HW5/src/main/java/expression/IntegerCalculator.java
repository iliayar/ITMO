package expression;

import expression.Calculator;

public class IntegerCalculator implements Calculator<Integer> {

    public Integer add(Integer a, Integer b) {
        return a + b;
    }

    public Integer multiply(Integer a, Integer b) {
        return a * b;
    }

    public Integer divide(Integer a, Integer b) {
        return a / b;
    }

    public Integer substract(Integer a, Integer b) {
        return a - b;
    }

    public Integer negate(Integer a) {
        return -a;
    }

    public Integer parseNumber(String s) {
        return Integer.parseInt(s);
    }

}

package expression;

public class Count<T extends Number> extends UnaryOperation<T> {
    public Count(CommonExpression<T> a, Calculator<T> calc) {
        super(a, calc);
    }

    @Override
    public String getSymbol() {
        return "count";
    }

    @Override
    public CommonExpression getFirst() {
        return null;
    }

    @Override
    public CommonExpression getSecond() {
        return null;
    }

    protected T eval(T a) {
        // System.err.println("Count " + a.toString() + " = " + calc.count(a).toString());
        return calc.count(a);
    }

    @Override
    public int getPrior() {
        return 0;
    }
}

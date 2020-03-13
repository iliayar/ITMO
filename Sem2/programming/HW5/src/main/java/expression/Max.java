package expression;

public class Max<T extends Number> extends Operation<T> {

    public Max(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "max";
    }

    @Override
    protected T eval(T a, T b) {
        return calc.max(a, b);
    }

    @Override
    public int getPrior() {
        return 3;
    }

    @Override
    public boolean isCommutative() {
        return true;
    }

}

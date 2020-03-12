package expression;

public class Min<T extends Number> extends Operation<T> {

    public Min(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "min";
    }

    @Override
    protected T eval(T a, T b) {
        return calc.min(a, b);
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

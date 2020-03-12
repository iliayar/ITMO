package expression;

public class Subtract<T extends Number> extends Operation<T>{
    public Subtract(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }

    @Override
    public String getSymbol() {
        return "-";
    }

    @Override
    protected T eval(T a, T b) {
        // System.err.println("TEST");
        return calc.subtract(a, b);
    }


    @Override
    public int getPrior() {
        return 2;
    }

    @Override
    public boolean isCommutative() {
        return false;
    }
}

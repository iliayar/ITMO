package expression;

public class Multiply extends Operation {
    public Multiply(Expression a, Expression b) {
        super(a, b);
    }

    @Override
    protected String getSymbol() {
        return "*";
    }

    @Override
    protected int eval(int a, int b) {
        return a*b;
    }

    @Override
    public int getPrior() {
        return 2;
    }
}

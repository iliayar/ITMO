package expression;

public class Add extends Operation {

    public Add(CommonExpression a, CommonExpression b) {
        super(a,b);
    }

    @Override
    protected String getSymbol() {
        return "+";
    }

    @Override
    protected int eval(int a, int b) {
        return a + b;
    }

    @Override
    public int getPrior() {
        return 3;
    }

}

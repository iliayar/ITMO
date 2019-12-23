package expression;

public class Inverse extends UnaryOperation {
    public Inverse(Expression a) {
        super(a);
    }

    @Override
    public String getSymbol() {
        return "-";
    }

    @Override
    public CommonExpression getFirst() {
        return null;
    }

    @Override
    public CommonExpression getSecond() {
        return null;
    }

    @Override
    protected int eval(int a) {
        return -a;
    }


    @Override
    public int getPrior() {
        return 0;
    }
}

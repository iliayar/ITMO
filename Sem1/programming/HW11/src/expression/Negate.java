package expression;

public class Negate extends UnaryOperation {
    public Negate(Expression a) {
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

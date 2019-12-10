package expression;

public class Subtract extends Operation{
    public Subtract(ExpressionMember a, ExpressionMember b) {
        super(a, b);
    }

    @Override
    protected String getSymbol() {
        return "-";
    }

    @Override
    protected int eval(int a, int b) {
        return a - b;
    }

    @Override
    public int getPrior() {
        return 4;
    }
}

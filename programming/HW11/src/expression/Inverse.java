package expression;

public class Inverse extends UnaryOperation {
    public Inverse(Expression a) {
        super(a);
    }

    @Override
    protected String getSymbol() {
        return "-";
    }

    @Override
    protected int eval(int a) {
        return -a;
    }

    @Override
    protected long eval(long a) {
        return -a;
    }


    @Override
    public int getPrior() {
        return 0;
    }
}

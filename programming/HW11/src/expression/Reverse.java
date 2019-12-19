package expression;

public class Reverse extends UnaryOperation {
    public Reverse(Expression a) {
        super(a);
    }

    @Override
    protected String getSymbol() {
        return "reverse ";
    }

    @Override
    protected int eval(int a) {
        boolean isMinus = a < 0;
        a = a < 0 ? -a : a;
        int res = 0;
        while(a > 0) {
            res = res*10 + a%10;
            a /= 10;
        }

        return isMinus ? -res : res;
    }

    @Override
    public int getPrior() {
        return 0;
    }
}

package expression;

public class Digits extends UnaryOperation {

    public Digits(Expression a) {
        super(a);
    }

    @Override
    protected String getSymbol() {
        return "digits ";
    }

    @Override
    protected int eval(int a) {
        a = a < 0 ? -a : a;

        int res = 0;
        while(a > 0) {
            res += a%10;
            a /=10;
        }
        return res;
    }

    @Override
    public int getPrior() {
        return 0;
    }
}

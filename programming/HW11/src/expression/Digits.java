package expression;

import java.math.BigInteger;

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
        long tmp = a;
        tmp = tmp < 0 ? -tmp : tmp;

        long res = 0;
        while(tmp > 0) {
            res += tmp%10;
            tmp /=10;
        }
        return (int)res;
    }



    @Override
    public int getPrior() {
        return 0;
    }
}

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
//        System.out.println("Reversing int " + a);
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
    protected long eval(long a) {
//        System.out.println("Reversing long " + a);
        boolean isMinus = a < 0;
        a = a < 0 ? -a : a;
        long res = 0;
        while(a > 0) {
            res = res*10 + (int)a%10;
            a /= 10;
        }
//        System.out.println("Result " + res);
        return isMinus ? -res : res;
    }


    @Override
    public int getPrior() {
        return 0;
    }
}

package expression;

public class Reverse extends UnaryOperation {
    public Reverse(Expression a) {
        super(a);
    }

    @Override
    public String getSymbol() {
        return "reverse ";
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
//        System.out.println("Reversing int " + a);
        long tmp = a;
        boolean isMinus = a < 0;
        tmp = tmp < 0 ? -tmp : tmp;
        long res = 0;
        while(tmp > 0) {
            res = res*10 + tmp%10;
            tmp /= 10;
        }

        return (int) (isMinus ? -res : res);
    }



    @Override
    public int getPrior() {
        return 0;
    }
}

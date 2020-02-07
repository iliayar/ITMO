package expression.exceptions;

import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Operation;

public class Pow extends Operation {


    public Pow(CommonExpression a, CommonExpression b)
    {
        super(a,b);
    }


    @Override
    public int getPrior() {
        return 4;
    }

    @Override
    public boolean isCommutative() {
        return false;
    }

    @Override
    public String getSymbol() {
        return "**";
    }

    public int eval(int a, int b) {

        int res = a;

        for(int i = 0; i < b - 1; ++i) {
            if((long)res * (long)res > Integer.MAX_VALUE ||
                    (long)res * (long)res < Integer.MIN_VALUE) {
                throw new IntegerOverflowException(a + "**" + b);
            }
            res *= res;
        }

        return res;
    }
}

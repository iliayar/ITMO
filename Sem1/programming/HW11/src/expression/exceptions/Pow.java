package expression.exceptions;

import expression.CommonExpression;
import expression.DivisonByZeroException;
import expression.IntegerOverflowException;
import expression.Operation;

public class Pow extends Operation {


    public Pow(CommonExpression a, CommonExpression b)
    {
        super(a,b);
    }


    @Override
    public int getPrior() {
        return -1;
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

        if(b < 0 || (a == 0 && b == 0)) {
            throw new DivisonByZeroException(a,b);
        }

        int res = 1;

        for(int i = 0; i < b; ++i) {
            if((long)res * (long)a > Integer.MAX_VALUE ||
                    (long)res * (long)a < Integer.MIN_VALUE) {
                throw new IntegerOverflowException(a + "**" + b);
            }
            res *= a;
        }

        return res;
    }
}
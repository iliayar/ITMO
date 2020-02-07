package expression.exceptions;

import expression.CommonExpression;
import expression.DivisonByZeroException;
import expression.IntegerOverflowException;
import expression.Operation;

public class Log extends Operation {


    public Log(CommonExpression a, CommonExpression b)
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
        return "//";
    }

    public int eval(int a, int b) {

        int res = 0;

        if(b == 0) {
            throw new DivisonByZeroException(a,b);
        }

        while(a > 0) {
            a /= b;
        }

        return res;
    }
}

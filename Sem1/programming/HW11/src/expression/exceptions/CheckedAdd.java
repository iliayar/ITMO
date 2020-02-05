package expression.exceptions;

import expression.Add;
import expression.CommonExpression;
import expression.IntegerOverflowException;

public class CheckedAdd extends Add {


    public CheckedAdd(CommonExpression a, CommonExpression b) {
        super(a, b);
    }


    public int eval(int a, int b) throws IntegerOverflowException {

        if((long)a + (long)b > Integer.MAX_VALUE ||
                (long)a + (long)b < Integer.MIN_VALUE) {
            throw new IntegerOverflowException(a+"+"+b);
        }

        return a + b;
    }
}

package expression.exceptions;

import expression.Add;
import expression.CommonExpression;
import expression.IntegerOverflowException;

public class CheckedAdd extends Add {


    public CheckedAdd(CommonExpression a, CommonExpression b) {
        super(a, b);
    }


    public int eval(int a, int b) {

        if ((a > 0 && b > 0 && a > Integer.MAX_VALUE - b) ||
                (a < 0 && b < 0 && a < Integer.MIN_VALUE - b)) {
            throw new IntegerOverflowException(a+"+"+b);
        }

        return a + b;
    }
}

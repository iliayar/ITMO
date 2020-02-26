package expression.exceptions;

import expression.Add;
import expression.CommonExpression;
import expression.IntegerOverflowException;

public class CheckedAdd extends Add {


    public CheckedAdd(CommonExpression a, CommonExpression b) {
        super(a, b);
    }

    public static void checkOverflow(int a, int b, String msg) {
        if ((a > 0 && b > 0 && a > Integer.MAX_VALUE - b) ||
            (a < 0 && b < 0 && a < Integer.MIN_VALUE - b)) {
            throw new IntegerOverflowException(msg);
        }
    }


    public int eval(int a, int b) {

        // if ((a > 0 && b > 0 && a > Integer.MAX_VALUE - b) ||
        //         (a < 0 && b < 0 && a < Integer.MIN_VALUE - b)) {
        //     throw new IntegerOverflowException(a+"+"+b);
        // }
        checkOverflow(a,b,a + "+" + b);

        return a + b;
    }
}

package expression.exceptions;

import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Subtract;

public class CheckedSubtract extends Subtract {
    public CheckedSubtract(CommonExpression a, CommonExpression b) {
        super(a, b);
    }

    public static void checkOverflow(int a, int b, String msg) {
        if ((a >= 0 && b < 0 && a > Integer.MAX_VALUE + b) ||
            (a <= 0 && b > 0 && a < Integer.MIN_VALUE + b)) {
            throw new IntegerOverflowException(msg);
        }
    }

    @Override
    public int eval(int a, int b) {
        // if ((long)a - (long)b < Integer.MIN_VALUE ||
        //         (long)a - (long)b > Integer.MAX_VALUE) {
        //     throw new IntegerOverflowException(a+"-"+b);
        // }
        checkOverflow(a, b, a + " - " + b);

        return a - b;
    }
}

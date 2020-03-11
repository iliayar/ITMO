package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Multiply;

public class CheckedMultiply extends Multiply {
    public CheckedMultiply(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a, b, calc);
    }

    public static void checkOverflow(int a, int b, String msg) {
        if ((a > 0 && ((b > 0 && b > Integer.MAX_VALUE / a) || (b < 0 && b < Integer.MIN_VALUE / a))) ||
                (a < 0 && ((b > 0 && a < Integer.MIN_VALUE / b) || (b < 0 && b < Integer.MAX_VALUE / a)))) {
            throw new IntegerOverflowException(msg);
        }
    }
    @Override
    public Number eval(Number a, Number b) {
        // checkOverflow(a,b, a + "*" + b);

        return calc.multiply(a,b);
    }
}

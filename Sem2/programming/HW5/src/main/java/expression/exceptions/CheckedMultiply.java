package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.NumberOverflowException;
import expression.Multiply;

public class CheckedMultiply<T extends Number> extends Multiply<T> {
    public CheckedMultiply(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b,calc );
    }

    public static void checkOverflow(int a, int b, String msg) {
        if ((a > 0 && ((b > 0 && b > Integer.MAX_VALUE / a) || (b < 0 && b < Integer.MIN_VALUE / a))) ||
                (a < 0 && ((b > 0 && a < Integer.MIN_VALUE / b) || (b < 0 && b < Integer.MAX_VALUE / a)))) {
            throw new NumberOverflowException(msg);
        }
    }
    @Override
    public T eval(T a, T b) {
        // checkOverflow(a,b, a + "*" + b);

        return calc.multiply(a,b);
    }
}

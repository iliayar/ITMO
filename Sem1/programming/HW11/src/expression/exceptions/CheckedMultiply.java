package expression.exceptions;

import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Multiply;

public class CheckedMultiply extends Multiply {
    public CheckedMultiply(CommonExpression a, CommonExpression b) {
        super(a, b);
    }


    @Override
    public int eval(int a, int b) {
        if((a > 0 && ((b > 0 && b > Integer.MAX_VALUE/a) || (b < 0 && b < Integer.MIN_VALUE/a))) ||
                (a < 0 && ((b > 0 && a < Integer.MIN_VALUE/b) || (b < 0 && b < Integer.MAX_VALUE/a)))) {

            throw new IntegerOverflowException(a+"*"+b);
        }

        return a*b;
    }
}

package expression.exceptions;

import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Subtract;

public class CheckedSubtract extends Subtract {
    public CheckedSubtract(CommonExpression a, CommonExpression b) {
        super(a, b);
    }


    @Override
    public int eval(int a, int b) {
        if((long)a - (long)b < Integer.MIN_VALUE ||
                (long)a - (long)b > Integer.MAX_VALUE) {
            throw new IntegerOverflowException(a+"-"+b);
        }

        return a - b;
    }
}

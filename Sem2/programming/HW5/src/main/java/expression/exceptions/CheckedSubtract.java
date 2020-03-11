package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Subtract;

public class CheckedSubtract extends Subtract {
    public CheckedSubtract(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a, b, calc);
    }


    @Override
    public Number eval(Number a, Number b) {
        // if((long)a - (long)b < Integer.MIN_VALUE ||
        //         (long)a - (long)b > Integer.MAX_VALUE) {
        //     throw new IntegerOverflowException(a+"-"+b);
        // }

        return calc.substract(a, b);
    }
}

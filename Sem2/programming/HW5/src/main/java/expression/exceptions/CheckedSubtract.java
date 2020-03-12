package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Subtract;

public class CheckedSubtract<T extends Number> extends Subtract<T> {
    public CheckedSubtract(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }


    @Override
    public T eval(T a, T b) {
        // if((long)a - (long)b < Integer.MIN_VALUE ||
        //         (long)a - (long)b > Integer.MAX_VALUE) {
        //     throw new IntegerOverflowException(a+"-"+b);
        // }

        return calc.subtract(a, b);
    }
}

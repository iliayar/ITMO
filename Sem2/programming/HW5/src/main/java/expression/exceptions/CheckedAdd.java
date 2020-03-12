package expression.exceptions;

import expression.Add;
import expression.Calculator;
import expression.CommonExpression;
import expression.NumberOverflowException;

public class CheckedAdd<T extends Number> extends Add<T> {


    public CheckedAdd(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }


    public T eval(T a, T b) {

        // if((a > 0 && b > 0 && a > calc.MAX_VALUE - b) ||
        //         (a < 0 && b < 0 && a < calc.MIN_VALUE - b)) {
        //     throw new IntegerOverflowException(a+"+"+b);
        // }

        return calc.add(a, b);
    }
}

package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.Divide;
import expression.DivisonByZeroException;
import expression.IntegerOverflowException;

public class CheckedDivide<T extends Number> extends Divide<T> {
    public CheckedDivide(CommonExpression<T> a, CommonExpression<T> b, Calculator<T> calc) {
        super(a, b, calc);
    }


    @Override
    public T eval(T a, T b) {
        // if(b == 0) {
        //     throw new DivisonByZeroException(a,b);
        // }
        // if(b == -1 && a == Integer.MIN_VALUE) {
        //     throw new IntegerOverflowException(a+"+"+b);
        // }
        return calc.divide(a, b);
    }
}

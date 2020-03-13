package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.NumberOverflowException;
import expression.Negate;

public class CheckedNegate<T extends Number> extends Negate<T> {
    public CheckedNegate(CommonExpression<T> a, Calculator<T> calc) {
        super(a, calc);
    }

    @Override
    protected T eval(T a) {
        // if(a == Integer.MIN_VALUE) {
        //     throw new IntegerOverflowException("-"+a);
        // }

        return calc.negate(a);
    }
}

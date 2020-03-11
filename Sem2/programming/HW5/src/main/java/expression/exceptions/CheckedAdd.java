package expression.exceptions;

import expression.Add;
import expression.Calculator;
import expression.CommonExpression;
import expression.IntegerOverflowException;

public class CheckedAdd extends Add {


    public CheckedAdd(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a, b, calc);
    }


    public Number eval(Number a, Number b) {

        // if((a > 0 && b > 0 && a > calc.MAX_VALUE - b) ||
        //         (a < 0 && b < 0 && a < calc.MIN_VALUE - b)) {
        //     throw new IntegerOverflowException(a+"+"+b);
        // }

        return calc.add(a, b);
    }
}

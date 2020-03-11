package expression.exceptions;

import expression.Calculator;
import expression.CommonExpression;
import expression.Divide;
import expression.DivisonByZeroException;
import expression.IntegerOverflowException;

public class CheckedDivide extends Divide {
    public CheckedDivide(CommonExpression a, CommonExpression b, Calculator calc) {
        super(a, b, calc);
    }


    @Override
    public Number eval(Number a, Number b) {
        // if(b == 0) {
        //     throw new DivisonByZeroException(a,b);
        // }
        // if(b == -1 && a == Integer.MIN_VALUE) {
        //     throw new IntegerOverflowException(a+"+"+b);
        // }
        return calc.divide(a, b);
    }
}

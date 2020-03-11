package expression.exceptions;

import expression.Calculator;
import expression.Expression;
import expression.IntegerOverflowException;
import expression.Negate;

public class CheckedNegate extends Negate {
    public CheckedNegate(Expression a, Calculator calc) {
        super(a, calc);
    }

    @Override
    protected Number eval(Number a) {
        // if(a == Integer.MIN_VALUE) {
        //     throw new IntegerOverflowException("-"+a);
        // }

        return calc.negate(a);
    }
}

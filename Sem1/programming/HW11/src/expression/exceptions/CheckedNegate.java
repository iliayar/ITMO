package expression.exceptions;

import expression.Expression;
import expression.IntegerOverflowException;
import expression.Negate;

public class CheckedNegate extends Negate {
    public CheckedNegate(Expression a) {
        super(a);
    }

    @Override
    protected int eval(int a) {
        if(-(long)a > Integer.MAX_VALUE) {
            throw new IntegerOverflowException("-"+a);
        }

        return -a;
    }
}

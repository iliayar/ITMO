package expression.exceptions;

import expression.CommonExpression;
import expression.IntegerOverflowException;
import expression.Operation;

public class Pow extends Operation {


    public Pow(CommonExpression a, CommonExpression b)
    {
        super(a,b);
    }


    @Override
    public int getPrior() {
        return -1;
    }

    @Override
    public boolean isCommutative() {
        return false;
    }

    @Override
    public String getSymbol() {
        return "**";
    }

    public int eval(int a, int b) {
        int at = a, bt = b;
        if (b < 0 || (a == 0 && b == 0)) {
            throw new PowException(a, b);
        }

        int res = 1;

        while (b > 0) {
            if (b % 2 == 1){
                CheckedMultiply.checkOverflow(res,a, at + "**" + bt);
                res *= a;
                b -= 1;
            } else {
                CheckedMultiply.checkOverflow(a, a, at + "**" + bt);
                a *= a;
                b /= 2;
            }
        }

        return res;
    }
}

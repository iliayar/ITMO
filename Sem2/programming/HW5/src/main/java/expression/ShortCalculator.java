package expression;

import expression.NumberOverflowException;
import jdk.jfr.Unsigned;

public class ShortCalculator extends AbstractCalculator<Short> {


    public ShortCalculator(boolean checked) {
        super(checked);
    }

    public ShortCalculator() {
        super();
    }

    @Override
    public Short add(Short a, Short b) {
        checkAdd(a, b, Short.MAX_VALUE, Short.MIN_VALUE);
        // return Short.valueOf(Integer.valueOf(a + b).toString());
        return (short) (a + b);
    }

    @Override
    public Short divide(Short a, Short b) {
        checkDivide(a, b, Short.MAX_VALUE, Short.MIN_VALUE);
        // return Short.valueOf(Integer.valueOf(a / b).toString());
        return (short) (a / b);
    }

    @Override
    public Short multiply(Short a, Short b) {
        checkMultiply(a, b, Short.MAX_VALUE, Short.MIN_VALUE);
        // return Short.valueOf(Integer.valueOf(a * b).toString());
        return (short) (a * b);
    }

    @Override
    public Short negate(Short a) {
        checkNegate(a, Short.MAX_VALUE, Short.MIN_VALUE);
        // return Short.valueOf(Integer.valueOf(-a).toString());
        return (short) (-a);
    }

    @Override
    public Short parseNumber(String s) {
        // try {
        return Short.valueOf(s);
        // } catch(NumberFormatException e) {
        //     if(!checked) {
        //         return null;
        //     } else {
        //         throw new NumberOverflowException(s);
        //     }
        // }
    }

    @Override
    public Short subtract(Short a, Short b) {
        checkSubtract(a, b, Short.MAX_VALUE, Short.MIN_VALUE);
        // return Short.valueOf(Integer.valueOf(a - b).toString());
        return (short) (a - b);
    }

    @Override
    public Short valueOf(int n) {
        return (short)(int)Integer.valueOf(n);
    }

    @Override
    public int compareTo(Short n, Short a) {
        return Short.compare(n, a);
    }        // short t = a;
        // if(t < 0) {
        //     t += Short.MAX_VALUE - 3;
        // }


	@Override
	public Short count(Short a) {
      return Short.valueOf(Integer.valueOf(Integer.bitCount(a.intValue() & 0xFFFF)).toString());
	}
}

package expression;

import java.math.BigInteger;

public class Const extends Operand {

    int value;

    public Const(int v) {
        this.value = v;
    }

    public Const(long v) {
        this.value = (int)v;
    }

    @Override
    protected String getSymbol() {
        return Integer.toString(value);
    }

    @Override
    protected int getValue(int x) {
        return value;
    }


    @Override
    protected int getValue(int x, int y, int z) {
        return value;
    }

    @Override
    protected BigInteger getValue(BigInteger x, BigInteger y, BigInteger z) {
        return BigInteger.valueOf(value);
    }

    //    @Override
    public int getPrior() {
        return 0;
    }
}

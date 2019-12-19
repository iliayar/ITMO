package expression;

import java.math.BigInteger;

public class Variable extends Operand {

    String symbol;

    public Variable(String s) {
        this.symbol = s;
    }

    @Override
    protected String getSymbol() {
        return symbol;
    }

    @Override
    protected int getValue(int x) {
        return x;
    }
    
    @Override
    protected int getValue(int x, int y, int z) {
        switch(symbol) {
            case "x":
                return x;
            case "y":
                return y;
            case "z":
                return z;
        }
        return 0;
    }

    @Override
    protected BigInteger getValue(BigInteger x, BigInteger y, BigInteger z) {
        return BigInteger.valueOf(getValue(x.intValue(), y.intValue(), z.intValue()));
    }

    //    @Override
    public int getPrior() {
        return 0;
    }

}

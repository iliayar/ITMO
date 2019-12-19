package expression;

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
    protected long getValue(long x, long y, long z) {
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

//    @Override
    public int getPrior() {
        return 0;
    }

}

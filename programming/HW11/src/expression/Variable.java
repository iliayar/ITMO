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
    public int getPrior() {
        return 0;
    }

}

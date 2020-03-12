package expression;

public class Variable<T extends Number> extends Operand<T> {

    String symbol;

    public Variable(String s) {
        this.symbol = s;
    }

    @Override
    public String getSymbol() {
        return symbol;
    }

    @Override
    public CommonExpression getFirst() {
        return this;
    }

    @Override
    public CommonExpression getSecond() {
        return this;
    }

    @Override
    protected T getValue(T x) {
        return x;
    }

    @Override
    protected T getValue(T x, T y, T z) {
        switch(symbol) {
            case "x":
                return x;
            case "y":
                return y;
            case "z":
                return z;
        }
        return null;
    }

    @Override
    public boolean equals(Object expr) {
        if( !(expr instanceof CommonExpression)) {
            return false;
        }
        return getSymbol().equals(((CommonExpression) expr).getSymbol());
    }


    //    @Override
    public int getPrior() {
        return 0;
    }

	@Override
	public int hashCode() {
      return (symbol.codePointAt(0)*BASE*BASE + MOD) % MOD;
	}

}

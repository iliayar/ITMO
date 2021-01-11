package expression;

public class Const<T extends Number> extends Operand<T> {

    T value;

    public Const(T v) {
        this.value = v;
    }
    
    @Override
    public String getSymbol() {
        return value.toString();
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
    public boolean equals(Object expr) {
        if( !(expr instanceof CommonExpression)) {
            return false;
        }
        return getSymbol().equals(((CommonExpression) expr).getSymbol());
    }


    @Override
    protected T getValue(T x) {
        return value;
    }


    @Override
    protected T getValue(T x, T y, T z) {
        return value;
    }

    //    @Override
    public int getPrior() {
        return 0;
    }

	@Override
	public int hashCode() {
      return (value.intValue()*BASE + MOD) % MOD;
	}
}

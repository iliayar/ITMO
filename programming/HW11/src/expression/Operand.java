package expression;

public abstract class Operand implements CommonExpression {

    @Override
    public int evaluate(int x) {
        return getValue(x);
    }

    @Override public int evaluate(int x, int y, int z) {
        return getValue(x,y,z);
    }

    @Override
    public String toString(){
        return getSymbol();
    }

    @Override
    public String toMiniString(){
        return getSymbol();
    }

    @Override
    public boolean equals(Object expr) {
        if( !(expr instanceof CommonExpression)) {
            return false;
        }
        return ((CommonExpression)expr).toString().equals(this.toString());
    }

    @Override
    public int hashCode() {
        return (getValue(BASE)*BASE + MOD) % MOD;
    }

    @Override
    public boolean isCommutative() {
        return true;
    }

    @Override
    public boolean isIntSafe() {
        return true;
    }

    protected abstract String getSymbol();
    protected abstract int getValue(int x);
    protected abstract int getValue(int x, int y, int z);
}

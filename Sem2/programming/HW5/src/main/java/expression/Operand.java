package expression;

public abstract class Operand<T extends Number> implements CommonExpression<T> {

    @Override
    public T evaluate(T x) {
        return getValue(x);
    }

    @Override
    public T evaluate(T x, T y, T z) {
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
        return expr.toString().equals(this.toString());
    }

    @Override
    public boolean isCommutative() {
        return true;
    }

    @Override
    public boolean isIntSafe() {
        return true;
    }

    public abstract String getSymbol();
    protected abstract T getValue(T x);
    protected abstract T getValue(T x, T y, T z);
}

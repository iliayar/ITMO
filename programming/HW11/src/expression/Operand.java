package expression;

public abstract class Operand implements Expression {

    @Override
    public int evaluate(int x) {
        return getValue(x);
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
    public boolean equals(Expression expr) {
        return expr.toString().equals(toString());
    }

    protected abstract String getSymbol();
    protected abstract int getValue(int x);
}

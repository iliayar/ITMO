package expression;

public abstract class Operand implements ExpressionMember {

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
    public boolean equals(Object expr) {
        if( !(expr instanceof ExpressionMember)) {
            return false;
        }
        return ((ExpressionMember)expr).toString().equals(this.toString());
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    protected abstract String getSymbol();
    protected abstract int getValue(int x);
}

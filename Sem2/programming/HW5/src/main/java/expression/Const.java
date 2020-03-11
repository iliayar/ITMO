package expression;

public class Const extends Operand {

    Number value;

    public Const(Number v) {
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
    protected Number getValue(Number x) {
        return value;
    }


    @Override
    protected Number getValue(Number x, Number y, Number z) {
        return value;
    }

    //    @Override
    public int getPrior() {
        return 0;
    }
}

package expression;

public class Const extends Operand {

    int value;

    public Const(int v) {
        this.value = v;
    }
    
    @Override
    public String getSymbol() {
        return Integer.toString(value);
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
    protected int getValue(int x) {
        return value;
    }


    @Override
    protected int getValue(int x, int y, int z) {
        return value;
    }

    //    @Override
    public int getPrior() {
        return 0;
    }
}

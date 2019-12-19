package expression;

import java.math.BigInteger;

public abstract class UnaryOperation implements CommonExpression {
    CommonExpression a;

    public UnaryOperation(Expression a) {
        this.a = (CommonExpression) a;
    }

    @Override
    public int evaluate(int x) {
        return eval(a.evaluate(x));
    }

    @Override
    public int evaluate(int x, int y, int z) {
        int resA, resB;
        return (int)eval(a.evaluate(x,y,z));
    }

    @Override
    public String toString() {
        return "(" + getSymbol() + "(" + a.toString() + "))";
    }

    @Override
    public String toMiniString() {
        String res = "";

        res += "(" + getSymbol();

        if(a.getPrior() >= 3) {
            res += "(" + a.toMiniString() + ")";
        } else {
            res += a.toMiniString();
        }

        res += ")";

        return res;
    }

    @Override
    public boolean equals(Object expr) {
        if(!(expr instanceof CommonExpression)) {
            return false;
        }
//        System.err.println(this.toString());
//        System.err.println(expr.toString());
        return ((CommonExpression)expr).toString().equals(this.toString());
//        return true;
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
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
    protected abstract int eval(int a);

}

package expression;

import java.util.Objects;

public abstract class Operation implements CommonExpression {

    CommonExpression a;
    CommonExpression b;

    protected Operation(Expression a, Expression b) {
        this.a = (CommonExpression) a;
        this.b = (CommonExpression) b;
    }

    @Override
    public int evaluate(int x) {
        return eval(a.evaluate(x), b.evaluate(x));
    }


    @Override
    public int evaluate(int x, int y, int z) {
        return eval(a.evaluate(x,y,z), b.evaluate(x,y,z));
    }

    @Override
    public String toString() {
        return "(" + a.toString() + " " + getSymbol() + " " + b.toString() + ")";
    }

    @Override
    public String toMiniString() {
        StringBuilder res = new StringBuilder();

        if(getPrior() < a.getPrior()) {
            res.append("(");
            res.append(a.toMiniString());
            res.append(")");
        } else {
            res.append(a.toMiniString());
        }

        res.append(" ").append(getSymbol()).append(" ");

        if(getPrior() < b.getPrior() ||
                ((!isCommutative() || !b.isIntSafe()) && getPrior() <= b.getPrior())) {
            res.append("(");
            res.append(b.toMiniString());
            res.append(")");
        } else {
            res.append(b.toMiniString());
        }

        return res.toString();
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Operation operation = (Operation) o;
        return Objects.equals(a, operation.a) &&
                Objects.equals(b, operation.b) &&
                Objects.equals(getSymbol(), operation.getSymbol());
    }

    @Override
    public int hashCode() {
        String s = getSymbol();
        int res = 0;
        for(int i = 0; i < s.length(); ++i) {
            res = res*BASE + s.charAt(i);
            res %= MOD;
        }
        return (a.hashCode()*BASE*BASE*BASE + res*BASE*BASE + b.hashCode()*BASE) % MOD;
//        return toString().hashCode();
    }

    @Override
    public boolean isIntSafe() {
        return true;
    }

    @Override
    public CommonExpression getFirst() {
        return a;
    }


    @Override
    public CommonExpression getSecond() {
        return b;
    }

    public abstract String getSymbol();
    protected abstract int eval(int a, int b);
}

package expression;

public abstract class Operation implements CommonExpression {

    CommonExpression a;
    CommonExpression b;

    public Operation(Expression a, Expression b) {
        this.a = (CommonExpression) a;
        this.b = (CommonExpression) b;
    }

    @Override
    public int evaluate(int x) {
        int resA, resB;
        return eval(a.evaluate(x), b.evaluate(x));
    }

    @Override
    public int evaluate(int x, int y, int z) {
        return (int)eval(a.evaluate((long)x,y,z), b.evaluate((long)x,y,z));
    }

    @Override
    public long evaluate(long x, long y, long z) {
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

        res.append(" " + getSymbol() + " ");

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
    public boolean equals(Object expr) {
        if(!(expr instanceof CommonExpression)) {
            return false;
        }

//        System.err.println(this.toString());
//        System.err.println(expr.toString());
        return ((CommonExpression)expr).hashCode() == this.hashCode();
//        return true;
    }

    @Override
    public int hashCode() {
        String s = getSymbol();
        int res = 0;
        for(int i = 0; i < s.length(); ++i) {
            res = res*BASE + s.charAt(i);
            res %= MOD;
        }
        return (a.hashCode()*BASE + res + b.hashCode()) % MOD;
    }

    @Override
    public boolean isIntSafe() {
        return true;
    }

    protected abstract String getSymbol();
    protected abstract int eval(int a, int b);
    protected abstract long eval(long a, long b);
}

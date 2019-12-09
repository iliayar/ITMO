package expression;

public abstract class Operation implements Expression {

    Expression a;
    Expression b;

    public Operation(Expression a, Expression b) {
        this.a = a;
        this.b = b;
    }

    @Override
    public int evaluate(int x) {
        int resA, resB;
        return eval(a.evaluate(x), b.evaluate(x));
    }

    @Override
    public String toString() {
        return "(" + a.toString() + " " + getSymbol() + " " + b.toString() + ")";
    }

    @Override
    public String toMiniString() {
        String res = "";

        if(a.getPrior() > getPrior() ||
                (a.getPrior() == getPrior() && (a.getPrior() == 3 || a.getPrior() == 1))) {
            res += "(" + a.toMiniString() + ")";
        } else {
            res += a.toMiniString();
        }
        res += " " + getSymbol() + " ";
        if(b.getPrior() > getPrior() ||
                (a.getPrior() == getPrior() && (a.getPrior() == 3 || a.getPrior() == 1))) {
            res += "(" + b.toMiniString() + ")";
        } else {
            res += b.toMiniString();
        }
        return res;
    }

    @Override
    public boolean equals(Expression expr) {
        return toString().equals(expr.toString());
    }

    protected abstract String getSymbol();
    protected abstract int eval(int a, int b);
}

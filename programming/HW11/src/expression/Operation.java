package expression;

public abstract class Operation implements ExpressionMember {

    ExpressionMember a;
    ExpressionMember b;

    public Operation(Expression a, Expression b) {
        this.a = (ExpressionMember) a;
        this.b = (ExpressionMember) b;
    }

    @Override
    public int evaluate(int x) {
        int resA, resB;
        return eval(a.evaluate(x), b.evaluate(x));
    }

    @Override
    public int evaluate(int x, int y, int z) {
        int resA, resB;
        return eval(a.evaluate(x,y,z), b.evaluate(x,y,z));
    }

    @Override
    public String toString() {
        return "(" + a.toString() + " " + getSymbol() + " " + b.toString() + ")";
    }

    @Override
    public String toMiniString() {
        String res = "";

        if(getPrior() < a.getPrior() - 1 + a.getPrior()%2) {
            res += "(" + a.toMiniString() + ")";
        } else {
            res += a.toMiniString();
        }

        res += " " + getSymbol() + " ";

        if(getPrior() < b.getPrior() || (getPrior()%2 == 0 && b.getPrior()%2 == 0 && b.getPrior() != 0) ||
                (getPrior() == 4 && b.getPrior() >= 3) || (getPrior() == 2 && b.getPrior() < 3 && b.getPrior() != 0)) {
            res += "(" + b.toMiniString() + ")";
        } else {
            res += b.toMiniString();
        }

        return res;
    }

    @Override
    public boolean equals(Object expr) {
        if(!(expr instanceof ExpressionMember)) {
            return false;
        }
//        System.err.println(this.toString());
//        System.err.println(expr.toString());
        return ((ExpressionMember)expr).toString().equals(this.toString());
//        return true;
    }

    @Override
    public int hashCode() {
        return this.toString().hashCode();
    }

    protected abstract String getSymbol();
    protected abstract int eval(int a, int b);
}

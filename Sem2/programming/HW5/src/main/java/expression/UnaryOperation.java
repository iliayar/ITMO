package expression;

public abstract class UnaryOperation<T extends Number> implements CommonExpression<T> {
    CommonExpression<T> a;

    protected Calculator<T> calc;

    public UnaryOperation(CommonExpression<T> a, Calculator<T> calc) {
        this.a = a;
        this.calc = calc;
    }

    @Override
    public T evaluate(T x) {
        return eval(a.evaluate(x));
    }

    @Override
    public T evaluate(T x, T y, T z) {
        Number resA, resB;
        return eval(a.evaluate(x,y,z));
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

    public abstract String getSymbol();
    protected abstract T eval(T a);

}

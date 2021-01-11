package expression;

public class DivisonByZeroException  extends  ExpressionException{

    public <T> DivisonByZeroException(T a, T b) {
        super("Divison by zero happens when: " + a.toString() + "/" + b.toString());
    }
}

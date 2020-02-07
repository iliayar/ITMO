package expression;

public class DivisonByZeroException  extends  ExpressionException{

    public DivisonByZeroException(int a, int b) {
        super("Divison by zero happens when: " + a + "/" + b);
    }
}

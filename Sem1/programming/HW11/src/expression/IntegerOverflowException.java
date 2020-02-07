package expression;

public class IntegerOverflowException extends ExpressionException {

    public IntegerOverflowException(String operation) {
        super("Overflow happens when: " + operation);
    }

}

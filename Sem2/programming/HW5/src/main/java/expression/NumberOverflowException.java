package expression;

public class NumberOverflowException extends ExpressionException {

    public NumberOverflowException(String operation) {
        super("Overflow happens when: " + operation);
    }

}

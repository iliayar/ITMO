package expression.exceptions;

import expression.ExpressionException;

public class PowException extends ExpressionException {
    public PowException(int a, int b) {
        super("Error when trying " + a + " ** " + b);
    }
}

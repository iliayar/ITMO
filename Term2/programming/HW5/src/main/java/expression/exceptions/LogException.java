package expression.exceptions;

import expression.ExpressionException;

public class LogException extends ExpressionException {
    public LogException(int a, int b) {
        super("Error when trying " + a + " // " + b);
    }
}

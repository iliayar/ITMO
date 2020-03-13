package expression.parser;

import expression.ExpressionException;

public class ParserException extends ExpressionException {
    public ParserException(final String message) {
        super(message);
    }
}
